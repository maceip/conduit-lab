import React, { useEffect, useState } from 'react';
import { IxToggle } from '@siemens/ix-react';
import { loadJson, fmtDate, crateOk, trustedTotal, NR, REPO, blobUrl, type Ratchet, type Stats } from './data';
import { Stat, ShimDiagram } from './parts';
import SectionVerus from './SectionVerus';
import SectionWhy from './SectionWhy';
import SectionStatus from './SectionStatus';
import SectionCoverage from './SectionCoverage';

export default function App() {
  const [ratchet, setRatchet] = useState<Ratchet | null>(null);
  const [stats, setStats] = useState<Stats | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [theme, setTheme] = useState<'dark' | 'light'>(() =>
    localStorage.getItem('conduit-theme') === 'light' ? 'light' : 'dark',
  );

  useEffect(() => {
    document.documentElement.setAttribute('data-ix-theme', 'classic');
    document.documentElement.setAttribute('data-ix-color-schema', theme);
    localStorage.setItem('conduit-theme', theme);
  }, [theme]);

  useEffect(() => {
    (async () => {
      const [r, s] = await Promise.allSettled([
        loadJson<Ratchet>('browser/ratchet.json'),
        loadJson<Stats>('data/stats.json'),
      ]);
      const problems: string[] = [];
      if (r.status === 'fulfilled') setRatchet(r.value);
      else problems.push(`browser/ratchet.json (${(r.reason as Error)?.message ?? r.reason})`);
      if (s.status === 'fulfilled') setStats(s.value);
      else problems.push(`data/stats.json (${(s.reason as Error)?.message ?? s.reason})`);
      if (problems.length) {
        setError(
          `Could not load ${problems.join(' and ')}. Metrics are hidden, not guessed — regenerate them with scripts/ratchet.py and scripts/collect_stats.py.`,
        );
      }
    })();
  }, []);

  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const ok = crateOk(vurl);
  const trusted = trustedTotal(vurl);
  const z3 = stats?.toolchains?.z3;
  const z3ver = z3 ? (z3.match(/version ([\d.]+)/) ?? [null, z3])[1] ?? z3 : null;

  return (
    <div className="wb-page">
      <header className="wb-top">
        <span className="wb-brand">CONDUIT // VERIFIED BROWSER</span>
        <nav className="wb-nav" aria-label="Chapters">
          <a href="#verus">01 Verus</a>
          <a href="#why">02 Why hard</a>
          <a href="#status">03 Status</a>
          <a href="#coverage">Coverage</a>
          <a href="#arch">Architecture</a>
        </nav>
        <span className="sp" />
        <div className="wb-top-links">
          <a className="wb-link" href={blobUrl('docs/verified-browser-engine.md')} target="_blank" rel="noreferrer">
            Design doc
          </a>
          <a className="wb-link" href="irrigation.html">Irrigation demo</a>
          <a className="wb-link" href={REPO} target="_blank" rel="noreferrer">GitHub</a>
          <IxToggle
            checked={theme === 'light'}
            textOn="Light"
            textOff="Dark"
            onCheckedChange={(e) => setTheme(e.detail ? 'light' : 'dark')}
          />
        </div>
      </header>

      <div className="wb-scoreboard" data-testid="ratchet-stats">
        <div className="wb-metrics">
          <Stat value={vurl ? String(vurl.verified) : NR} label="verified functions" tone={ok ? 'verified' : 'critical'} />
          <Stat value={trusted === null ? NR : String(trusted)} label="trusted items" tone={trusted === 0 ? 'verified' : 'critical'} />
          <Stat value={vurl ? `${vurl.verify_seconds}s` : NR} label="re-verify time" />
          <Stat
            value={vurl ? `${vurl.tests_passed}/${vurl.tests_passed + vurl.tests_failed}` : NR}
            label="WPT + diff tests"
            tone={vurl && vurl.tests_failed === 0 ? 'verified' : 'critical'}
          />
        </div>
        <div className="wb-chips">
          <span className="wb-chip">whatwg/url @4f461b81 · pinned</span>
          <span className="wb-chip">verus {ratchet?.verus ?? NR} · upstream</span>
          {z3ver && <span className="wb-chip">z3 {z3ver} · arm64</span>}
        </div>
      </div>

      {error && (
        <div className="wb-load-error" role="alert" data-testid="load-error">
          {error}
        </div>
      )}

      <main className="wb-main">
        <SectionVerus />
        <SectionWhy ratchet={ratchet} />
        <SectionStatus ratchet={ratchet} />
        <SectionCoverage />
        <section className="wb-row12" id="arch">
          <div className="wb-c12 wb-col">
            <div className="wb-chapter">03 · Architecture</div>
            <h2 className="wb-h2">The verified shim</h2>
            <ShimDiagram />
          </div>
        </section>
      </main>

      <footer className="wb-footer" data-testid="provenance-footer">
        <span>
          Every metric loads from{' '}
          <a className="wb-link" href="browser/ratchet.json">browser/ratchet.json</a> +{' '}
          <a className="wb-link" href="data/stats.json">data/stats.json</a> — nothing is hand-typed.
        </span>
        <span data-testid="footer-generated">
          ratchet {fmtDate(ratchet?.generated_at)} · stats {fmtDate(stats?.generated_at)}
        </span>
      </footer>
    </div>
  );
}