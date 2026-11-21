import React, { useEffect, useState } from 'react';
import { IxToggle } from '@siemens/ix-react';
import { loadJson, fmtDate, crateOk, trustedTotal, NR, REPO, blobUrl, type Ratchet, type Stats } from './data';
import { Stat, ShimDiagram } from './parts';
import { CVES } from './content/cves';
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
          <a href="#coverage">01 The bugs</a>
          <a href="#verus">02 Proofs</a>
          <a href="#why">03 Scope</a>
          <a href="#arch">04 Design</a>
          <a href="#status">05 Status</a>
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

      <section className="wb-lede" data-testid="lede">
        <h1 className="wb-h1">A browser engine with its security-critical code proved, one component at a time</h1>
        <p className="wb-prose">
          Of the last {CVES.length} Chrome bugs Google confirmed attackers were exploiting,{' '}
          {CVES.filter((c) => c.component.startsWith('V8')).length} were in V8, the JavaScript
          engine. Most of those are type confusion or out-of-bounds access: the engine
          assumed something about an object's layout that an attacker made false. This project
          is building a browser where those assumptions are checked theorems. Each component is
          written in Rust and checked by Verus, which uses the Z3 solver to show the code does
          what its published standard says for every possible input.
        </p>
        <p className="wb-prose">
          One component exists so far. <code>vurl</code> implements the WHATWG URL standard's
          percent-encoding, IPv4 and IPv6 algorithms, and every function in it is proved equal to
          a line-by-line transcription of the standard. The numbers below are read from the
          last verifier run. Code that is not proved gets counted as trusted, and the design rule
          is that the trusted count never rises between releases.
        </p>
      </section>

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
        <SectionCoverage />
        <SectionVerus />
        <SectionWhy ratchet={ratchet} />
        <section className="wb-row12" id="arch">
          <div className="wb-c12 wb-col">
            <div className="wb-chapter">04 · Design</div>
            <h2 className="wb-h2">A proved kernel in front of untrusted renderers</h2>
            <p className="wb-prose">
              Each site gets its own renderer process running an ordinary, unverified engine
              (html5ever for HTML, Stylo for CSS, a GPU stack for drawing). A renderer cannot open
              a socket, read a cookie or change the address bar itself. It asks over typed IPC, and
              the kernel, written in Verus, decides. The kernel owns the network parsers, the
              origin and cookie policy, tab management and the address bar. Verified components
              then replace renderer parts one at a time, starting with the JavaScript engine.
            </p>
            <ShimDiagram />
          </div>
        </section>
        <SectionStatus ratchet={ratchet} />
      </main>

      <footer className="wb-footer" data-testid="provenance-footer">
        <span>
          Every number on this page is read at load time from{' '}
          <a className="wb-link" href="browser/ratchet.json">browser/ratchet.json</a> and{' '}
          <a className="wb-link" href="data/stats.json">data/stats.json</a>, which the verifier and collector write.
        </span>
        <span data-testid="footer-generated">
          ratchet {fmtDate(ratchet?.generated_at)} · stats {fmtDate(stats?.generated_at)}
        </span>
      </footer>
    </div>
  );
}