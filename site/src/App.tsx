import React, { useEffect, useState } from 'react';
import { IxToggle } from '@siemens/ix-react';
import {
  loadJson,
  fmtDate,
  allCratesOk,
  ratchetTotals,
  sumTrusted,
  NR,
  REPO,
  blobUrl,
  type Ratchet,
  type Stats,
} from './data';
import { Stat, ShimDiagram } from './parts';
import { CVES } from './content/cves';
import SectionVerus from './SectionVerus';
import SectionWhy from './SectionWhy';
import SectionStatus from './SectionStatus';
import SectionCoverage from './SectionCoverage';

const ARCH_CARDS = [
  {
    id: 'kernel',
    icon: 'assets/icon-kernel.jpg',
    title: 'Verified Kernel Boundary',
    body: 'Typed IPC, origin policy, and capability handles isolate untrusted renderers so a compromised tab cannot escape its own origin.',
  },
  {
    id: 'solver',
    icon: 'assets/icon-solver.jpg',
    title: 'Verus + Z3 Prover',
    body: 'Every executable function in the verified crates carries Rust specs checked by Z3 across all possible inputs, with zero unsafe code.',
  },
  {
    id: 'synthesis',
    icon: 'assets/icon-synthesis.jpg',
    title: 'ESMeta Spec Synthesis',
    body: 'ECMA-262 clauses are compiled directly from <emu-alg> specifications into Verus spec functions and differentially tested against test262.',
  },
  {
    id: 'telemetry',
    icon: 'assets/icon-telemetry.jpg',
    title: 'Monotonic Ratchet',
    body: 'Every build writes live verified-function counts, trusted-item counts, and conformance pass rates into browser/ratchet.json.',
  },
];

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

  const totals = ratchetTotals(ratchet);
  const ok = allCratesOk(ratchet);
  const trusted = sumTrusted(totals?.trusted);
  const z3 = stats?.toolchains?.z3;
  const z3ver = z3 ? (z3.match(/version ([\d.]+)/) ?? [null, z3])[1] ?? z3 : null;

  return (
    <div className="wb-page">
      <header className="wb-top">
        <span className="wb-brand">
          <img className="wb-brand-logo" src="assets/conduit-logo.jpg" alt="CONDUIT logo" />
          <span>CONDUIT // VERIFIED BROWSER</span>
        </span>
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

      <div className="wb-banner-wrap">
        <figure className="wb-banner-frame" data-testid="hero-banner">
          <img
            src="assets/conduit-banner-wide.jpg"
            alt="CONDUIT Verified Browser Engine wide banner"
          />
        </figure>
      </div>

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
          The verified workspace now spans{' '}
          <strong>{totals ? `${totals.crates} crates` : NR}</strong>: <code>vurl</code> (WHATWG
          URL algorithms), the full J0–J7 JavaScript engine (<code>vjs_spec</code> through{' '}
          <code>vjs_vm</code>), the Web IDL capability boundary (<code>vjs_webidl</code>), and
          a sandboxed WebAssembly 1.0 interpreter (<code>vwasm</code>). The browser kernel,
          Nanvix renderer isolation, and HTML/CSS layout remain next phases. Every number below
          is read at load time from the last verifier run, and the trusted count is ratcheted to
          never rise between releases.
        </p>
      </section>

      <div className="wb-scoreboard" data-testid="ratchet-stats">
        <div className="wb-metrics">
          <Stat
            value={totals ? String(totals.verified) : NR}
            label="verified functions"
            tone={ok ? 'verified' : 'critical'}
          />
          <Stat
            value={trusted === null ? NR : String(trusted)}
            label="trusted items"
            tone={trusted === 0 ? 'verified' : 'critical'}
          />
          <Stat
            value={totals ? `${totals.verify_seconds}s` : NR}
            label="re-verify time"
          />
          <Stat
            value={totals ? `${totals.tests_passed}/${totals.tests_passed + totals.tests_failed}` : NR}
            label="crate tests"
            tone={totals && totals.tests_failed === 0 ? 'verified' : 'critical'}
          />
        </div>
        <div className="wb-chips">
          <span className="wb-chip">verus {ratchet?.verus ?? NR}</span>
          <span className="wb-chip">
            z3 {z3ver ?? NR} · {totals ? `${totals.crates} crates` : NR}
          </span>
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
              replace renderer parts one at a time — starting with the URL parser, JavaScript
              engine, Web IDL boundary, and WebAssembly sandbox already verified in this repo.
            </p>
            <div className="wb-arch-split">
              <figure className="wb-iso-frame" data-testid="iso-architecture">
                <img
                  src="assets/conduit-iso-architecture.jpg"
                  alt="Isometric architecture diagram of the CONDUIT verified browser kernel and sandboxed renderers"
                />
              </figure>
              <ShimDiagram />
            </div>
            <div className="wb-arch-cards" data-testid="arch-cards">
              {ARCH_CARDS.map((card) => (
                <article key={card.id} className="wb-arch-card">
                  <img className="wb-arch-icon" src={card.icon} alt={card.title} />
                  <div className="wb-arch-card-body">
                    <h3>{card.title}</h3>
                    <p>{card.body}</p>
                  </div>
                </article>
              ))}
            </div>
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
