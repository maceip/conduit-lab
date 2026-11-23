import React, { useEffect, useState } from 'react';
import {
  NR,
  REPO,
  allCratesOk,
  blobUrl,
  fmtDate,
  loadJson,
  ratchetTotals,
  sumDifferentialCases,
  sumTrusted,
  type Ratchet,
  type Stats,
} from './data';
import { IconArrowRight, IconCopy, IconExternal } from './icons';
import { AmbientMachineBackdrop, ArchitectureDiagram, PlateFrame, StatTile } from './parts';
import SectionCoverage from './SectionCoverage';
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
  const diffCases = sumDifferentialCases(ratchet?.test262_suites);
  const z3 = stats?.toolchains?.z3;
  const z3ver = z3 ? (z3.match(/version ([\d.]+)/) ?? [null, z3])[1] ?? z3 : null;

  const copyDigest = (id: string, value: string | null) => {
    if (!value) return;
    navigator.clipboard?.writeText(value).catch(() => {});
    setCopiedId(id);
    window.setTimeout(() => setCopiedId((prev) => (prev === id ? null : prev)), 1400);
  };

  return (
    <div className="ch-page-shell" id="top" data-testid="conduit-shell">
      <header className="ch-topbar">
        <a className="ch-brand" href="#top">
          <span className="ch-brand-dot" aria-hidden="true" />
          <span>CONDUIT</span>
        </a>

        <nav className="ch-nav" aria-label="Page sections">
          <a href="#arch">Architecture</a>
          <a href="#ratchet">Proofs</a>
          <a href="#scope">Scope</a>
          <a href="#coverage">CVEs</a>
        </nav>

        <div className="ch-topbar-right">
          <a className="ch-nav-link" href="workbench.html" data-testid="nav-workbench">
            Proof workbench
          </a>
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

          <button
            type="button"
            role="switch"
            aria-checked={theme === 'light'}
            aria-label="Toggle light theme"
            className="ch-theme-btn"
            data-testid="theme-switch"
            onClick={() => setTheme((prev) => (prev === 'dark' ? 'light' : 'dark'))}
          >
            <span className="ch-theme-dot" aria-hidden="true" />
            <span>{theme === 'dark' ? 'Dark' : 'Light'}</span>
          </button>
        </div>
      </header>

      {/* Opening Hero — Ambient Cutaway Turboprop Backdrop + Liquid Glass Thesis Card */}
      <section className="ch-hero" data-testid="lede">
        <AmbientMachineBackdrop
          machine="turboprop"
          theme={theme}
          testId="hero-turboprop-bg"
        />

        <div className="ch-hero-inner">
          <div className="ch-hero-glass" data-testid="hero-glass">
            <h1 className="ch-h1">
              Don’t test a browser engine for memory bugs. Prove they cannot exist.
            </h1>
            <p className="ch-hero-prose">
              CONDUIT proves URL parsing, JavaScript, Web IDL, and WebAssembly in Verus and
              Z3—eliminating memory-corruption and type-confusion bug classes across every input,
              with zero <code>unsafe</code> Rust.
            </p>
            <div className="ch-hero-actions">
              <a className="ch-cta-primary" href="workbench.html" data-testid="cta-workbench">
                <span>Open proof workbench</span>
                <IconArrowRight size={13} />
              </a>
              <a className="ch-cta-secondary" href="#ratchet">
                <span>Verified ledger</span>
              </a>
            </div>
          </div>
        </div>
      </section>

      {/* Quiet Hairline Ratchet Telemetry Strip */}
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
              value={diffCases !== null ? diffCases.toLocaleString('en-US') : NR}
              label="differential spec cases"
              hint="tc39/test262 · WHATWG · Wasm"
              tone={diffCases !== null ? (ok ? 'proved' : 'fail') : 'neutral'}
              testId="stat-differential cases"
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
                {ratchet?.inputs_sha256 ? ratchet.inputs_sha256.slice(0, 8) : NR}
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

      {/* Main Specification: Architecture (Maglev) -> Crates -> Scope -> CVE Baseline */}
      <main className="ch-spec-container">
        <section className="ch-spec-row" id="arch">
          <div className="ch-prose-col">
            <h2 className="ch-section-title">
              One proved kernel in front of disposable renderers
            </h2>
            <p className="ch-prose-text">
              Each web origin runs in a disposable renderer with zero socket, cookie, or
              cross-origin memory access. Privileged calls cross a narrow capability gap into the
              proved Verus kernel.
            </p>
            <ArchitectureDiagram />
          </div>

          <div className="ch-artifact-col">
            <PlateFrame
              machine="maglev"
              title="Shanghai SMT Maglev"
              subtitle="10 mm non-contact gap & phase-locked guideway"
              theme={theme}
              defaultPreset="assembled"
              testId="plate-maglev"
            />
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
  );
}
