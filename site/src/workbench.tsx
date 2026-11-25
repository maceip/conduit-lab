import React, { useEffect, useState } from 'react';
import { createRoot } from 'react-dom/client';
import './site.css';
import { NR, REPO, blobUrl, fmtDate, loadJson, type Ratchet } from './data';
import { ConduitWordmark, IconGitHub } from './icons';
import SectionVerus from './SectionVerus';

function WorkbenchApp() {
  const [ratchet, setRatchet] = useState<Ratchet | null>(null);
  const [error, setError] = useState<string | null>(null);
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
    loadJson<Ratchet>('browser/ratchet.json')
      .then((data) => {
        if (!cancelled) setRatchet(data);
      })
      .catch((err) => {
        if (!cancelled) {
          setError(
            `Could not load browser/ratchet.json (${(err as Error)?.message ?? err}). Live proof listings show "${NR}".`,
          );
        }
      });
    return () => {
      cancelled = true;
    };
  }, []);

  return (
    <div className="ch-page-shell" data-testid="workbench-shell">
      <header className="ch-topbar" data-testid="machined-topbar">
        <a
          className="ch-brand ch-alu-panel"
          href="./"
          data-testid="workbench-back"
          aria-label="Back to CONDUIT"
        >
          <span className="ch-brand-back" aria-hidden="true">
            ←
          </span>
          <ConduitWordmark />
        </a>

        <div className="ch-topbar-spacer" aria-hidden="true" />

        <div className="ch-topbar-right">
          <nav className="ch-nav" aria-label="Workbench navigation">
            <a className="ch-alu-btn" href="./#ratchet">
              Proofs
            </a>
          </nav>
          <a
            className="ch-nav-link ch-alu-btn"
            href={blobUrl('docs/verified-browser-engine.md')}
            target="_blank"
            rel="noreferrer"
          >
            Design doc
          </a>
          <a
            className="ch-nav-icon-link ch-alu-btn ch-alu-icon"
            href={REPO}
            target="_blank"
            rel="noreferrer"
            aria-label="CONDUIT on GitHub"
            title="GitHub repository"
            data-testid="nav-github"
          >
            <IconGitHub size={16} />
          </a>
        </div>
      </header>

      {error && (
        <div className="ch-load-error" role="alert" data-testid="load-error">
          {error}
        </div>
      )}

      <main className="ch-spec-container">
        <SectionVerus ratchet={ratchet} />
      </main>

      <footer className="ch-footer" data-testid="provenance-footer">
        <div className="ch-footer-left">
          <span className="ch-brand-dot" aria-hidden="true" />
          <span>
            <a className="ch-mono-link" href="browser/ratchet.json">
              browser/ratchet.json
            </a>
          </span>
        </div>
        <div className="ch-footer-right">
          <span>
            ratchet {fmtDate(ratchet?.generated_at)} · sha256{' '}
            <span title={ratchet?.inputs_sha256}>{ratchet?.inputs_sha256?.slice(0, 12) ?? NR}</span>
          </span>
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
      </footer>
    </div>
  );
}

createRoot(document.getElementById('root')!).render(<WorkbenchApp />);
