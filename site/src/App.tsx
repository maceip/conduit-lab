import React, { useEffect, useState } from 'react';
import {
  IxApplication,
  IxApplicationHeader,
  IxPaneLayout,
  IxPane,
  IxToggle,
} from '@siemens/ix-react';
import { IxDigestBadge } from '@maceip/ix-workbench-primitives';
import { loadJson, fmtDate, NR, REPO, blobUrl, type Ratchet, type Stats } from './data';
import PaneVerus from './PaneVerus';
import PaneWhyHard from './PaneWhyHard';
import PaneEngine from './PaneEngine';

const CHROME_H = 78; // 48px application header + 30px provenance footer

export default function App() {
  const [ratchet, setRatchet] = useState<Ratchet | null>(null);
  const [stats, setStats] = useState<Stats | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [theme, setTheme] = useState<'dark' | 'light'>(() =>
    localStorage.getItem('conduit-theme') === 'light' ? 'light' : 'dark',
  );
  const wide = window.matchMedia('(min-width: 1100px)').matches;
  const [leftOpen, setLeftOpen] = useState(wide);
  const [rightOpen, setRightOpen] = useState(wide);

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

  return (
    <IxApplication
      data-ix-theme="classic"
      data-ix-color-schema={theme}
      style={{ height: '100vh', width: '100vw' }}
    >
      <IxApplicationHeader name="CONDUIT // VERIFIED BROWSER">
        <div className="wb-header-links">
          <IxDigestBadge
            prefix="verus"
            digest={ratchet?.verus ?? NR}
            tone={ratchet ? 'verified' : 'neutral'}
            statusLabel={ratchet ? 'upstream' : 'no data'}
          />
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
      </IxApplicationHeader>

      {error && (
        <div className="wb-load-error" role="alert" data-testid="load-error">
          {error}
        </div>
      )}

      <IxPaneLayout
        layout="full-vertical"
        variant="inline"
        borderless={false}
        style={{ height: `calc(100vh - ${CHROME_H}px)`, width: '100%' }}
      >
        {/* Keep IxPane permanently mounted (toggle expanded) — siemens/ix #2904 */}
        <IxPane
          slot="left"
          heading="01 · What Verus is"
          size="33%"
          expanded={leftOpen}
          onExpandedChanged={(e) => setLeftOpen(e.detail.expanded)}
        >
          <div className="ix-slot-fill">
            <div className="ix-scroll-pane wb-pane-body">
              <PaneVerus ratchet={ratchet} />
            </div>
          </div>
        </IxPane>

        {/* Explicit slot="content" — siemens/ix #1302 */}
        <div slot="content" className="ix-slot-fill">
          <div className="wb-pane-head">
            <b>02</b> Why no verified Linux
          </div>
          <div className="ix-scroll-pane wb-pane-body">
            <PaneWhyHard ratchet={ratchet} />
          </div>
        </div>

        <IxPane
          slot="right"
          heading="03 · Where we are"
          size="33%"
          expanded={rightOpen}
          onExpandedChanged={(e) => setRightOpen(e.detail.expanded)}
        >
          <div className="ix-slot-fill">
            <div className="ix-scroll-pane wb-pane-body">
              <PaneEngine ratchet={ratchet} stats={stats} />
            </div>
          </div>
        </IxPane>
      </IxPaneLayout>

      <div className="wb-footer" data-testid="provenance-footer">
        <span>
          Every metric loads from{' '}
          <a className="wb-link" href="browser/ratchet.json">browser/ratchet.json</a> +{' '}
          <a className="wb-link" href="data/stats.json">data/stats.json</a> — nothing is hand-typed.
        </span>
        <span data-testid="footer-generated">
          ratchet {fmtDate(ratchet?.generated_at)} · stats {fmtDate(stats?.generated_at)}
        </span>
      </div>
    </IxApplication>
  );
}