import React, { useEffect, useRef, useState } from 'react';
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
  const initialThemeRef = useRef<'dark' | 'light'>(theme);

  useEffect(() => {
    document.documentElement.setAttribute('data-theme', theme);
    localStorage.setItem('conduit-theme', theme);
    document.querySelectorAll<HTMLIFrameElement>('iframe.ch-inkwork-frame').forEach((fr) => {
      fr.contentWindow?.postMessage({ type: 'conduit-theme', theme }, '*');
    });
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
        <header className="ch-topbar">
          <a className="ch-brand" href="#top">
            <span className="ch-brand-dot" aria-hidden="true" />
            <span>CONDUIT</span>
          </a>

          <nav className="ch-nav" aria-label="Page sections">
            <a href="#proofs">Proofs</a>
            <a href="#arch">Architecture</a>
            <a href="#ratchet">Crates</a>
            <a href="#scope">Scope</a>
            <a href="#coverage">CVEs</a>
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

        {/* Opening Hero — Copy + Illustration 1: Interactive Turboprop (V8 Engine Mapping) */}
        <section className="ch-hero" data-testid="lede">
          <div className="ch-hero-grid">
            <div className="ch-hero-copy">
              <h1 className="ch-h1">
                Don’t test a browser engine for memory bugs. Prove they cannot exist.
              </h1>
              <p className="ch-hero-prose">
                CONDUIT is a browser engine built with machine-checked Rust proofs in Verus and Z3.{' '}
                {v8Count} of the last {CVES.length} Chrome zero-days exploited unproved V8 memory or
                object-layout assumptions; here,{' '}
                <strong>{totals ? `${totals.crates} crates` : NR}</strong>—spanning URL parsing, the
                J0–J7 JavaScript engine, Web IDL capabilities, and WebAssembly 1.0—verify from
                scratch with zero <code>unsafe</code> code.
              </p>
              <div className="ch-hero-actions">
                <a className="ch-cta-primary" href="#proofs">
                  <span>Inspect a live proof</span>
                  <IconArrowRight size={14} />
                </a>
                <a className="ch-cta-secondary" href="#ratchet">
                  <span>Verified crate ledger</span>
                </a>
              </div>
            </div>

            <figure className="ch-plate-frame" data-testid="plate-turboprop">
              <iframe
                className="ch-inkwork-frame"
                src={`inkwork/index.html?embed=1&theme=${initialThemeRef.current}#turboprop`}
                title="Turboprop Engine — V8 JavaScript pipeline mapped across 31 parts and 6 sub-assemblies"
                onLoad={(ev) =>
                  ev.currentTarget.contentWindow?.postMessage({ type: 'conduit-theme', theme }, '*')
                }
              />
              <figcaption className="ch-plate-caption">
                <span>
                  <strong>FIG. 01 · Turboprop Engine</strong> — V8 subsystems mapped across 31 parts
                  &amp; 6 sub-assemblies
                </span>
                <span className="ch-mono">GW-TP-00</span>
              </figcaption>
            </figure>
          </div>
        </section>

        {/* Live Ratchet Scoreboard */}
        <section
          className="ch-scoreboard-strip"
          aria-label="Live Verification Ratchet Telemetry"
          data-testid="ratchet-stats"
        >
          <div className="ch-scoreboard-inner">
            <div className="ch-metrics-grid">
              <StatTile
                value={totals ? totals.verified.toLocaleString('en-US') : NR}
                label="verified proof queries"
                hint={
                  totals
                    ? `${totals.functions_by_mode.exec.toLocaleString('en-US')} exec · ${totals.functions_by_mode.proof.toLocaleString('en-US')} proof fns`
                    : undefined
                }
                tone={totals ? (ok ? 'proved' : 'fail') : 'neutral'}
                testId="stat-verified queries"
              />
              <StatTile
                value={trusted === null ? NR : String(trusted)}
                label="trusted items"
                hint="assume · admit · unsafe"
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
                hint={totals ? `${totals.crates} crates` : undefined}
                tone={totals ? (totals.tests_failed === 0 ? 'proved' : 'fail') : 'neutral'}
                testId="stat-crate tests"
              />
            </div>

            <div className="ch-digest-stack" data-testid="provenance-pills">
              <button
                type="button"
                className="ch-digest-pill"
                onClick={() => copyDigest('verus', ratchet?.verus ?? null)}
                title="Copy Verus toolchain revision"
              >
                <span className="ch-digest-left">
                  {copiedId === 'verus' ? 'copied' : `verus ${ratchet?.verus ?? NR}`}
                </span>
                <IconCopy size={11} />
              </button>

              <button
                type="button"
                className="ch-digest-pill"
                onClick={() => copyDigest('z3', z3ver)}
                title="Copy Z3 solver version"
              >
                <span className="ch-digest-left">
                  {copiedId === 'z3' ? 'copied' : `z3 ${z3ver ?? NR}`}
                </span>
                <span className="ch-digest-meta">
                  {totals ? `${totals.crates} crates` : NR}
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

        {/* Main Specification: Proofs -> Architecture (Maglev) -> Crates -> Scope -> Collapsed CVEs */}
        <main className="ch-spec-container">
          <SectionVerus ratchet={ratchet} />

          <section className="ch-spec-row" id="arch">
            <div className="ch-prose-col">
              <h2 className="ch-section-title">
                One proved kernel in front of disposable renderers
              </h2>
              <p className="ch-prose-text">
                Like a maglev car riding a 10 mm non-contact gap over a phase-locked stator beam,
                every web origin runs in an isolated renderer that never touches sockets, cross-site
                cookies, or the address bar—all privileged calls cross typed, capability-checked IPC
                into the Verus security kernel.
              </p>
              <ArchitectureDiagram />
            </div>

            <div className="ch-artifact-col">
              <figure className="ch-plate-frame" data-testid="plate-maglev">
                <iframe
                  className="ch-inkwork-frame"
                  src={`inkwork/index.html?embed=1&theme=${initialThemeRef.current}#maglev`}
                  title="Shanghai SMT Maglev — 10 mm non-contact levitation gap and synchronous long-stator guideway"
                  onLoad={(ev) =>
                    ev.currentTarget.contentWindow?.postMessage({ type: 'conduit-theme', theme }, '*')
                  }
                />
                <figcaption className="ch-plate-caption">
                  <span>
                    <strong>FIG. 02 · Shanghai SMT Maglev</strong> — 10 mm non-contact gap &amp;
                    synchronous stator guideway
                  </span>
                  <span className="ch-mono">GW-MV-00</span>
                </figcaption>
              </figure>
            </div>
          </section>

          <SectionStatus ratchet={ratchet} />
          <SectionWhy ratchet={ratchet} />
          <SectionCoverage />
        </main>

        <footer className="ch-footer" data-testid="provenance-footer">
          <div className="ch-footer-left">
            <span className="ch-brand-dot" aria-hidden="true" />
            <span>
              <a className="ch-mono-link" href="browser/ratchet.json">
                browser/ratchet.json
              </a>{' '}
              ·{' '}
              <a className="ch-mono-link" href="data/stats.json">
                data/stats.json
              </a>{' '}
              ·{' '}
              <a className="ch-mono-link" href="inkwork/index.html">
                Mechanical plates
              </a>{' '}
              ·{' '}
              <a
                className="ch-mono-link"
                href={blobUrl('docs/verified-browser-engine.md')}
                target="_blank"
                rel="noreferrer"
              >
                Design doc
              </a>
            </span>
          </div>
          <div className="ch-footer-right" data-testid="footer-generated">
            ratchet {fmtDate(ratchet?.generated_at)} · sha256{' '}
            <span title={ratchet?.inputs_sha256} data-testid="inputs-digest">
              {ratchet?.inputs_sha256?.slice(0, 12) ?? NR}
            </span>
          </div>
        </footer>
      </div>
    </ClickUIProvider>
  );
}
