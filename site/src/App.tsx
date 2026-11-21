import React, { useEffect, useState } from 'react';
import { ClickUIProvider, Switch } from '@clickhouse/click-ui';
import {
  NR,
  REPO,
  allCratesOk,
  blobUrl,
  fmtDate,
  loadJson,
  ratchetTotals,
  sumTrusted,
  type Ratchet,
  type Stats,
} from './data';
import { CVES } from './content/cves';
import { IconArrowRight, IconCopy, IconExternal } from './icons';
import { ArchitectureDiagram, StatTile } from './parts';
import SectionCoverage from './SectionCoverage';
import SectionVerus from './SectionVerus';
import SectionWhy from './SectionWhy';
import SectionStatus from './SectionStatus';

const HERO_V8_TRIO = [
  {
    key: 'hidden-classes',
    label: 'Hidden Classes (Map) · Automated Turret Punch Press',
    slug: 'fig-03-hidden-classes',
  },
  {
    key: 'ignition',
    label: 'Ignition Bytecode Interpreter · 24V Starter & Injection Rail',
    slug: 'fig-05-ignition',
  },
  {
    key: 'old-space',
    label: 'Orinoco Old Space · AS/RS High-Bay Warehouse',
    slug: 'fig-07-old-space',
  },
] as const;

export default function App() {
  const [ratchet, setRatchet] = useState<Ratchet | null>(null);
  const [stats, setStats] = useState<Stats | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [copiedId, setCopiedId] = useState<string | null>(null);
  const [frameHeights, setFrameHeights] = useState<Record<string, number>>({});
  const [theme, setTheme] = useState<'dark' | 'light'>(() =>
    typeof window !== 'undefined' && localStorage.getItem('conduit-theme') === 'light'
      ? 'light'
      : 'dark',
  );

  useEffect(() => {
    document.documentElement.setAttribute('data-theme', theme);
    localStorage.setItem('conduit-theme', theme);
    document.querySelectorAll<HTMLIFrameElement>('iframe.ch-hero-iso-frame').forEach((fr) => {
      fr.contentWindow?.postMessage({ type: 'v8-iso-theme', theme }, '*');
    });
  }, [theme]);

  useEffect(() => {
    const onMsg = (ev: MessageEvent) => {
      const data = ev.data as { type?: string; id?: string; height?: number } | null;
      if (data?.type === 'v8-iso-height' && data.id && typeof data.height === 'number' && data.height > 120) {
        setFrameHeights((prev) =>
          prev[data.id!] === data.height ? prev : { ...prev, [data.id!]: data.height! },
        );
      }
    };
    window.addEventListener('message', onMsg);
    return () => window.removeEventListener('message', onMsg);
  }, []);

  useEffect(() => {
    let cancelled = false;
    (async () => {
      const [r, s] = await Promise.allSettled([
        loadJson<Ratchet>('browser/ratchet.json'),
        loadJson<Stats>('data/stats.json'),
      ]);
      if (cancelled) return;
      const problems: string[] = [];
      if (r.status === 'fulfilled') setRatchet(r.value);
      else problems.push(`browser/ratchet.json (${(r.reason as Error)?.message ?? r.reason})`);
      if (s.status === 'fulfilled') setStats(s.value);
      else problems.push(`data/stats.json (${(s.reason as Error)?.message ?? s.reason})`);
      if (problems.length) {
        setError(
          `Could not load ${problems.join(' and ')}. Live metrics show "${NR}" instead of stale placeholders — regenerate with browser/scripts/ratchet.py and scripts/collect_stats.py.`,
        );
      }
    })();
    return () => {
      cancelled = true;
    };
  }, []);

  const totals = ratchetTotals(ratchet);
  const ok = allCratesOk(ratchet);
  const trusted = sumTrusted(totals?.trusted);
  const z3 = stats?.toolchains?.z3;
  const z3ver = z3 ? (z3.match(/version ([\d.]+)/) ?? [null, z3])[1] ?? z3 : null;
  const v8Count = CVES.filter((c) => c.component.startsWith('V8')).length;

  const copyDigest = (id: string, value: string | null) => {
    if (!value) return;
    navigator.clipboard?.writeText(value).catch(() => {});
    setCopiedId(id);
    window.setTimeout(() => setCopiedId((prev) => (prev === id ? null : prev)), 1400);
  };

  return (
    <ClickUIProvider theme={theme}>
      <div className="ch-page-shell" id="top" data-testid="conduit-shell">
        {/* Sticky Top Bar */}
        <header className="ch-topbar">
          <a className="ch-brand" href="#top">
            <img
              className="ch-brand-mark"
              src="assets/conduit-mark.png"
              alt="CONDUIT emblem"
              width={26}
              height={26}
            />
            <span>CONDUIT</span>
          </a>

          <nav className="ch-nav" aria-label="Page sections">
            <a href="#coverage">Zero-days</a>
            <a href="#proofs">Proofs</a>
            <a href="#scope">Why boundaries</a>
            <a href="#arch">Architecture</a>
            <a href="#ratchet">Live status</a>
          </nav>

          <div className="ch-topbar-right">
            <a
              className="ch-nav-link"
              href={blobUrl('docs/verified-browser-engine.md')}
              target="_blank"
              rel="noreferrer"
            >
              Design doc
            </a>
            <a className="ch-nav-link" href="v8-anatomy.html">
              V8 anatomy
            </a>
            <a className="ch-nav-link" href="irrigation.html">
              Irrigation demo
            </a>
            <a className="ch-nav-link" href={REPO} target="_blank" rel="noreferrer">
              GitHub <IconExternal size={11} />
            </a>

            <div className="ch-theme-toggle">
              <Switch
                checked={theme === 'light'}
                onCheckedChange={(checked: boolean) => setTheme(checked ? 'light' : 'dark')}
                aria-label="Toggle light theme"
                data-testid="theme-switch"
              />
              <span className="ch-theme-label">{theme === 'dark' ? 'Dark' : 'Light'}</span>
            </div>
          </div>
        </header>

        {/* Opening Hero — Text Framing a Central Frosted-Glass Band of 3 Interactive V8 Figures */}
        <section className="ch-hero" data-testid="lede">
          <div className="ch-hero-backdrop" data-testid="hero-visual" aria-hidden="true">
            <img
              src="assets/hero-modules-backdrop.webp"
              alt=""
              width={1920}
              height={1071}
            />
          </div>

          <div className="ch-hero-stack">
            {/* Upper text framing the frosted glass band */}
            <div className="ch-hero-band-copy ch-hero-band-top">
              <h1 className="ch-h1">
                Don’t test a browser engine for memory bugs. Prove they cannot exist.
              </h1>
              <p className="ch-hero-prose">
                {v8Count} of the last {CVES.length} Chrome zero-days exploited in the wild came
                from V8. Almost all of them started the same way: the JavaScript engine trusted an
                assumption about memory or object layout that an attacker broke. CONDUIT replaces
                those assumptions with machine-checked Rust proofs verified by Verus and Z3 across
                every possible input.
              </p>
            </div>

            {/* Middle Full-Width Frosted Glass Band Carrying the Best 3 Interactive V8 Figures */}
            <div className="ch-hero-glass" data-testid="hero-v8-band">
              <div className="ch-hero-glass-inner">
                <div className="ch-hero-glass-bar">
                  <div className="ch-hero-glass-heading">
                    <span className="ch-hero-glass-kicker">Tier-1 V8 mandatory core</span>
                    <span className="ch-hero-glass-sub">
                      Hidden-class turret dies, Ignition bytecode rail, and Orinoco AS/RS warehouse—interactive isometric models
                    </span>
                  </div>

                  <div className="ch-hero-glass-controls">
                    <a className="ch-hero-all-link" href="v8-anatomy.html">
                      <span>All 8 core figures</span>
                      <IconArrowRight size={13} />
                    </a>
                  </div>
                </div>

                <div className="ch-hero-trio" data-testid="hero-v8-trio">
                  {HERO_V8_TRIO.map((item) => {
                    const frameId = `hero-${item.slug}`;
                    const h = frameHeights[frameId];
                    return (
                      <div className="ch-hero-iso-card" key={item.key}>
                        <iframe
                          className="ch-hero-iso-frame"
                          title={item.label}
                          scrolling="no"
                          src={`v8-iso/pages/${item.slug}.html?embed=1&compact=1&theme=${theme}&id=${frameId}`}
                          style={h ? { height: `${h}px` } : undefined}
                        />
                      </div>
                    );
                  })}
                </div>
              </div>
            </div>

            {/* Lower text & CTAs framing below the frosted glass band */}
            <div className="ch-hero-band-copy ch-hero-band-bottom">
              <p className="ch-hero-prose">
                Today, <strong>{totals ? `${totals.crates} crates` : NR}</strong> verify from
                scratch with zero <code>unsafe</code> code and zero trusted shortcuts: URL parsing
                (<code>vurl</code>), the full J0–J7 JavaScript engine (<code>vjs_spec</code> to{' '}
                <code>vjs_vm</code>), the Web IDL capability layer (<code>vjs_webidl</code>), and
                a sandboxed WebAssembly 1.0 interpreter (<code>vwasm</code>). Next up: the browser
                security kernel, Nanvix per-site sandboxing, and HTML/CSS/XML integration.
              </p>
              <div className="ch-hero-actions">
                <a className="ch-cta-primary" href="#ratchet">
                  <span>Inspect the verified crates</span>
                  <IconArrowRight size={14} />
                </a>
                <a className="ch-cta-secondary" href="v8-anatomy.html" data-testid="cta-v8-anatomy">
                  <span>Explore all 8 V8 figures</span>
                </a>
                <a className="ch-cta-secondary" href="#proofs">
                  <span>See a live proof</span>
                </a>
              </div>
            </div>
          </div>
        </section>

        {/* Full-Width Live Ratchet Scoreboard */}
        <section
          className="ch-scoreboard-strip"
          aria-label="Live Verification Ratchet Telemetry"
          data-testid="ratchet-stats"
        >
          <div className="ch-scoreboard-inner">
            <div className="ch-metrics-grid">
              <StatTile
                value={totals ? totals.verified.toLocaleString('en-US') : NR}
                label="verified functions"
                hint={totals ? `across ${totals.crates} crates` : undefined}
                tone={totals ? (ok ? 'proved' : 'fail') : 'neutral'}
                testId="stat-verified functions"
              />
              <StatTile
                value={trusted === null ? NR : String(trusted)}
                label="trusted items"
                hint="assume · admit · external_body · unsafe"
                tone={trusted === null ? 'neutral' : trusted === 0 ? 'proved' : 'fail'}
                testId="stat-trusted items"
              />
              <StatTile
                value={totals ? `${totals.verify_seconds}s` : NR}
                label="re-verify time"
                hint={totals ? `${totals.source_lines.toLocaleString('en-US')} lines of Rust` : undefined}
                tone="neutral"
                testId="stat-re-verify time"
              />
              <StatTile
                value={
                  totals
                    ? `${totals.tests_passed}/${totals.tests_passed + totals.tests_failed}`
                    : NR
                }
                label="crate tests"
                hint={totals ? `${totals.test_seconds}s full suite` : undefined}
                tone={totals ? (totals.tests_failed === 0 ? 'proved' : 'fail') : 'neutral'}
                testId="stat-crate tests"
              />
            </div>

            {/* Strictly max 2 adjacent provenance pills */}
            <div className="ch-digest-stack" data-testid="provenance-pills">
              <button
                type="button"
                className="ch-digest-pill"
                onClick={() => copyDigest('verus', ratchet?.verus ?? null)}
                title="Copy upstream Verus version"
              >
                <span className="ch-digest-left">
                  <span className="ch-status-dot" data-tone={ratchet ? 'proved' : 'neutral'} />
                  <span>
                    verus {copiedId === 'verus' ? 'copied' : ratchet?.verus ?? NR}
                  </span>
                </span>
                <span className="ch-digest-meta">
                  upstream <IconCopy size={11} />
                </span>
              </button>

              <button
                type="button"
                className="ch-digest-pill"
                onClick={() => copyDigest('z3', z3ver)}
                title="Copy Z3 solver version"
              >
                <span className="ch-digest-left">
                  <span className="ch-status-dot" data-tone={z3ver ? 'proved' : 'neutral'} />
                  <span>
                    z3 {copiedId === 'z3' ? 'copied' : z3ver ?? NR}
                  </span>
                </span>
                <span className="ch-digest-meta">
                  {totals ? `${totals.crates} crates` : NR} <IconCopy size={11} />
                </span>
              </button>
            </div>
          </div>
        </section>

        {/* Translucent Drafter-Grid Hardware Pillars */}
        <section className="ch-hw-strip" aria-label="Core architecture pillars" data-testid="hardware-strip">
          <div className="ch-hw-grid">
            <a className="ch-hw-item" href="#arch">
              <img src="assets/hw-kernel.webp" alt="Verified security kernel conduit core" width={78} height={78} />
              <div>
                <div className="ch-hw-title">Kernel boundary</div>
                <div className="ch-hw-sub">Typed capability IPC gating disposable per-site renderers</div>
              </div>
            </a>
            <a className="ch-hw-item" href="#proofs">
              <img src="assets/hw-prover.webp" alt="Verus and Z3 SMT solver die" width={78} height={78} />
              <div>
                <div className="ch-hw-title">Verus + Z3 prover</div>
                <div className="ch-hw-sub">Exhaustive SMT proofs across every input, zero unsafe Rust</div>
              </div>
            </a>
            <a className="ch-hw-item" href="#scope">
              <img src="assets/hw-synthesis.webp" alt="ESMeta specification synthesis core" width={78} height={78} />
              <div>
                <div className="ch-hw-title">Spec synthesis</div>
                <div className="ch-hw-sub">Pinned ECMA-262 clauses compiled directly into Verus specs</div>
              </div>
            </a>
            <a className="ch-hw-item" href="#ratchet">
              <img src="assets/hw-waveform.webp" alt="Differential verification and VM speedup waveform" width={78} height={78} />
              <div>
                <div className="ch-hw-title">Differential ratchet</div>
                <div className="ch-hw-sub">Live WPT, test262, and Wasm checks that never regress</div>
              </div>
            </a>
          </div>
        </section>

        {error && (
          <div className="ch-load-error" role="alert" data-testid="load-error">
            {error}
          </div>
        )}

        {/* Executable Specification Sections */}
        <main className="ch-spec-container">
          <SectionCoverage />
          <SectionVerus ratchet={ratchet} />
          <SectionWhy ratchet={ratchet} />

          {/* Section 4: Architecture */}
          <section className="ch-arch-section" id="arch">
            <div className="ch-arch-header">
              <div className="ch-section-lead">
                <img
                  src="assets/sticker-lock.webp"
                  alt="Isolated capability padlock over circuit hexagon illustration"
                  className="ch-sticker-medallion"
                  width={76}
                  height={76}
                />
                <div>
                  <h2 className="ch-section-title">
                    One proved kernel in front of disposable renderers
                  </h2>
                  <p className="ch-prose-text">
                    Every site gets its own isolated renderer process for HTML (<code>html5ever</code>),
                    CSS (<code>Stylo</code>), XML, and GPU drawing. A renderer cannot open sockets,
                    read cookies, or touch the address bar—every privileged request crosses typed,
                    capability-checked IPC into the Verus kernel. Verified crates replace renderer
                    subsystems one by one, starting with <code>vurl</code>, <code>vjs</code>{' '}
                    (J0–J7), <code>vjs_webidl</code>, and <code>vwasm</code>. Release 1 ships with
                    no extension API, removing an entire recurring exploit surface.
                  </p>
                </div>
              </div>
            </div>

            <div className="ch-arch-split">
              <figure className="ch-iso-frame" data-testid="iso-architecture">
                <img
                  src="assets/conduit-arch-iso.webp"
                  alt="Isometric hardware diagram of the CONDUIT kernel core and isolated modules"
                  width={1080}
                  height={826}
                />
                <figcaption>
                  The verified kernel core routes typed capabilities between the SMT prover, spec
                  compiler, network boundary, and isolated per-site execution sandboxes.
                </figcaption>
              </figure>
              <ArchitectureDiagram />
            </div>
          </section>

          <SectionStatus ratchet={ratchet} />
        </main>

        {/* Provenance Footer */}
        <footer className="ch-footer" data-testid="provenance-footer">
          <div className="ch-footer-left">
            <img
              src="assets/conduit-mark.png"
              alt=""
              width={20}
              height={20}
              className="ch-footer-mark"
            />
            <span>
              Every figure loads live from{' '}
              <a className="ch-mono-link" href="browser/ratchet.json">
                browser/ratchet.json
              </a>{' '}
              and{' '}
              <a className="ch-mono-link" href="data/stats.json">
                data/stats.json
              </a>
              .{' '}
              <a className="ch-mono-link" href="v8-anatomy.html">
                V8 anatomy
              </a>
              {' · '}
              <a className="ch-mono-link" href="irrigation.html">
                Irrigation demo
              </a>
              {' · '}
              <a
                className="ch-mono-link"
                href={blobUrl('docs/verified-browser-engine.md')}
                target="_blank"
                rel="noreferrer"
              >
                Design doc
              </a>
              {' · '}
              <a className="ch-mono-link" href={REPO} target="_blank" rel="noreferrer">
                GitHub
              </a>
            </span>
          </div>
          <div className="ch-footer-right" data-testid="footer-generated">
            ratchet {fmtDate(ratchet?.generated_at)} · stats {fmtDate(stats?.generated_at)}
          </div>
        </footer>
      </div>
    </ClickUIProvider>
  );
}
