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

export default function App() {
  const [ratchet, setRatchet] = useState<Ratchet | null>(null);
  const [stats, setStats] = useState<Stats | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [copiedId, setCopiedId] = useState<string | null>(null);
  const [theme, setTheme] = useState<'dark' | 'light'>(() =>
    typeof window !== 'undefined' && localStorage.getItem('conduit-theme') === 'light'
      ? 'light'
      : 'dark',
  );

  useEffect(() => {
    document.documentElement.setAttribute('data-theme', theme);
    localStorage.setItem('conduit-theme', theme);
  }, [theme]);

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
          `Could not load ${problems.join(' and ')}. Live metrics are shown as "${NR}" instead of guessed — regenerate them with browser/scripts/ratchet.py and scripts/collect_stats.py.`,
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

          <nav className="ch-nav" aria-label="Specification chapters">
            <a href="#coverage">Threats</a>
            <a href="#proofs">Proofs</a>
            <a href="#scope">Scope</a>
            <a href="#arch">Architecture</a>
            <a href="#ratchet">Ratchet</a>
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

        {/* Opening Thesis Hero */}
        <section className="ch-hero" data-testid="lede">
          <div className="ch-hero-inner">
            <div className="ch-hero-copy">
              <h1 className="ch-h1">
                A browser engine proved one security boundary at a time
              </h1>
              <p className="ch-hero-prose">
                In the last {CVES.length} Chrome vulnerabilities Google confirmed attackers
                exploited in the wild, {v8Count} were in V8—mostly type confusion and out-of-bounds
                memory corruption where the engine assumed an object invariant an attacker broke.
                CONDUIT replaces those assumptions with machine-checked Rust theorems verified by
                Verus and Z3 across every possible input.
              </p>
              <p className="ch-hero-prose">
                The verified workspace spans{' '}
                <strong>{totals ? `${totals.crates} crates` : NR}</strong> with zero{' '}
                <code>unsafe</code> code: WHATWG URL parsing (<code>vurl</code>), the full J0–J7
                JavaScript engine (<code>vjs_spec</code> through <code>vjs_vm</code>), the
                capability-checked Web IDL boundary (<code>vjs_webidl</code>), and a sandboxed
                WebAssembly 1.0 interpreter (<code>vwasm</code>). Browser kernel isolation theorems,
                Nanvix per-site sandboxing, and HTML/CSS/XML integration are next.
              </p>
              <div className="ch-hero-actions">
                <a className="ch-cta-primary" href="#ratchet">
                  <span>Inspect verified crates</span>
                  <IconArrowRight size={14} />
                </a>
                <a className="ch-cta-secondary" href="#proofs">
                  <span>Explore a Verus proof</span>
                </a>
              </div>
            </div>

            <figure className="ch-hero-stage" data-testid="hero-visual">
              <img
                src="assets/hero-conduit-core.webp"
                alt="CONDUIT 3D verified core hardware emblem"
                width={380}
                height={380}
              />
              <figcaption className="ch-hero-caption">
                <span>Safe Rust · Verus SMT</span>
                <span>Zero trusted hatches</span>
              </figcaption>
            </figure>
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
                hint={totals ? `${totals.source_lines.toLocaleString('en-US')} source LOC` : undefined}
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
                hint={totals ? `${totals.test_seconds}s test suite` : undefined}
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
                title="Copy upstream Verus toolchain version"
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

        {error && (
          <div className="ch-load-error" role="alert" data-testid="load-error">
            {error}
          </div>
        )}

        {/* Tufte 2-Column Executable Specification Sections */}
        <main className="ch-spec-container">
          <SectionCoverage />
          <SectionVerus ratchet={ratchet} />
          <SectionWhy ratchet={ratchet} />

          {/* Section 4: Architecture — Verified Kernel & Per-Site Sandboxes */}
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
                    A proved security kernel gating untrusted per-site renderers
                  </h2>
                  <p className="ch-prose-text">
                    Each origin runs inside its own isolated renderer process—handling HTML
                    (<code>html5ever</code>), CSS (<code>Stylo</code>), XML parsing, and per-site
                    GPU work. A renderer cannot open sockets, read cookies, or alter the address
                    bar directly; every privileged action crosses typed Vest-encoded IPC into the
                    Verus kernel. Verified components replace renderer layers one crate at a time,
                    starting with <code>vurl</code>, <code>vjs</code> (J0–J7),{' '}
                    <code>vjs_webidl</code>, and <code>vwasm</code>. Release 1 ships without an
                    extension API to eliminate that entire exploit class.
                  </p>
                </div>
              </div>
            </div>

            <div className="ch-arch-split">
              <figure className="ch-iso-frame" data-testid="iso-architecture">
                <img
                  src="assets/conduit-arch-iso.webp"
                  alt="Isometric hardware diagram of the CONDUIT kernel core and isolated verification modules"
                  width={1080}
                  height={826}
                />
                <figcaption>
                  Central verified conduit core connected over isolated channels to SMT solver,
                  spec compiler, capability router, and sandboxed execution nodes.
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
              Every number loads at runtime from{' '}
              <a className="ch-mono-link" href="browser/ratchet.json">
                browser/ratchet.json
              </a>{' '}
              and{' '}
              <a className="ch-mono-link" href="data/stats.json">
                data/stats.json
              </a>{' '}
              — zero hand-typed telemetry.{' '}
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
