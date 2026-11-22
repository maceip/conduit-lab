# CONDUIT Layouts & App Shell

The site is a **single-route React SPA** with a fixed page shell. There is no router library —
`site/src/main.tsx` mounts `site/src/App.tsx` into `#root`, and `App.tsx` renders the entire
document: topbar → hero → scoreboard strip → hardware pillar strip → main spec container →
provenance footer.

The app shell lives in **`site/src/App.tsx`** (490 lines). It is both the layout and the only page.

---

## `site/src/main.tsx` — FULL SOURCE (5 lines)

```tsx
import { createRoot } from 'react-dom/client';
import './site.css';
import App from './App';

createRoot(document.getElementById('root')!).render(<App />);
```

---

## `site/src/App.tsx` — FULL SOURCE (490 lines)

```tsx
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
                label="verified proof queries"
                hint={
                  totals
                    ? `${totals.functions_by_mode.exec.toLocaleString('en-US')} exec · ${totals.functions_by_mode.proof.toLocaleString('en-US')} proof fns, ${totals.crates} crates`
                    : undefined
                }
                tone={totals ? (ok ? 'proved' : 'fail') : 'neutral'}
                testId="stat-verified queries"
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
            ratchet {fmtDate(ratchet?.generated_at)} · inputs{' '}
            <span title={ratchet?.inputs_sha256} data-testid="inputs-digest">
              {ratchet?.inputs_sha256?.slice(0, 12) ?? NR}
            </span>{' '}
            · stats {fmtDate(stats?.generated_at)}
          </div>
        </footer>
      </div>
    </ClickUIProvider>
  );
}
```

---

## `site/index.html` — FULL SOURCE (69 lines)

```html
<!DOCTYPE html>
<html lang="en" data-theme="dark">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>CONDUIT — Formally Verified Browser Engine</title>
  <meta name="description" content="A browser engine whose security-critical components are proved in Rust with Verus and Z3: WHATWG URL, full J0–J7 JavaScript engine, Web IDL capability boundary, and sandboxed WebAssembly 1.0, backed by live ratchet telemetry.">
  <meta property="og:title" content="CONDUIT — Formally Verified Browser Engine">
  <meta property="og:description" content="Formally verified browser engine components in safe Rust with Verus and Z3, mapped against real exploited Chrome zero-days with live ratchet telemetry.">
  <meta property="og:image" content="assets/conduit-banner-wide.jpg">
  <meta name="twitter:card" content="summary_large_image">
  <link rel="icon" type="image/png" href="assets/conduit-favicon.png">
  <style>
    /* @font-face declarations for Archivo, Manrope, JetBrains Mono — see theme.md §2b */
  </style>
</head>
<body>
  <div id="root"></div>
  <noscript>This page requires JavaScript to fetch live verification telemetry from browser/ratchet.json and data/stats.json.</noscript>
  <script type="module" src="/src/main.tsx"></script>
</body>
</html>
```

---

## Shell CSS — `site/src/site.css:136-235` (topbar) + `236-545` (hero) + `546-771` (strips)

### Page shell + topbar — `site.css:136-235`

```css
.ch-page-shell {
  min-height: 100vh;
  display: flex;
  flex-direction: column;
  background: var(--ch-bg-canvas);
  color: var(--ch-text-primary);
}

.ch-topbar {
  position: sticky;
  top: 0;
  z-index: 30;
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 20px;
  min-height: 54px;
  padding: 8px 28px;
  background: var(--ch-bg-bar);
  border-bottom: 1px solid var(--ch-border-subtle);
}

.ch-brand {
  display: inline-flex;
  align-items: center;
  gap: 10px;
  font-family: var(--ch-font-display);
  font-size: 15px;
  font-weight: 700;
  letter-spacing: 0.1em;
  color: var(--ch-text-primary);
  text-decoration: none;
  flex-shrink: 0;
}

.ch-brand-mark {
  display: block;
  border-radius: 5px;
  border: 1px solid var(--ch-border-subtle);
}

.ch-nav {
  display: flex;
  align-items: center;
  gap: 18px;
  flex-wrap: wrap;
}

.ch-nav a {
  font-size: 13px;
  font-weight: 500;
  color: var(--ch-text-secondary);
  text-decoration: none;
  padding: 4px 0;
  transition: color 120ms ease;
}

.ch-nav a:hover { color: var(--ch-accent-text); }

.ch-topbar-right {
  display: flex;
  align-items: center;
  gap: 16px;
  font-size: 13px;
  flex-wrap: wrap;
}

.ch-nav-link {
  display: inline-flex;
  align-items: center;
  gap: 4px;
  color: var(--ch-text-secondary);
  text-decoration: none;
  transition: color 120ms ease;
}

.ch-nav-link:hover { color: var(--ch-accent-text); }

.ch-theme-toggle {
  display: inline-flex;
  align-items: center;
  gap: 7px;
  padding-left: 10px;
  border-left: 1px solid var(--ch-border-subtle);
}

.ch-theme-label {
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  color: var(--ch-text-secondary);
  min-width: 34px;
}
```

### Hero — `site.css:236-545`

```css
.ch-hero {
  position: relative;
  border-bottom: 1px solid var(--ch-border-subtle);
  background-color: #12151c;
  overflow: hidden;
  padding: 40px 0 44px;
  display: block;
}

[data-theme='light'] .ch-hero { background-color: #eaedf3; }

.ch-hero-backdrop {
  position: absolute;
  inset: 0;
  pointer-events: none;
  z-index: 1;
}

.ch-hero-backdrop::after {
  content: '';
  position: absolute;
  inset: 0;
  background: linear-gradient(
    90deg,
    rgba(11, 14, 20, 0.90) 0%,
    rgba(13, 16, 23, 0.78) 54%,
    rgba(16, 20, 28, 0.52) 100%
  );
}

[data-theme='light'] .ch-hero-backdrop::after {
  background: linear-gradient(
    90deg,
    rgba(247, 249, 253, 0.92) 0%,
    rgba(245, 248, 252, 0.84) 56%,
    rgba(242, 246, 251, 0.66) 100%
  );
}

.ch-hero-backdrop img {
  display: block;
  width: 100%;
  height: 100%;
  object-fit: cover;
  object-position: right center;
}

.ch-hero-stack {
  position: relative;
  z-index: 2;
  display: flex;
  flex-direction: column;
  gap: 24px;
  width: 100%;
}

.ch-hero-band-copy {
  max-width: 1380px;
  width: 100%;
  margin: 0 auto;
  padding: 0 28px;
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.ch-hero-band-top .ch-h1,
.ch-hero-band-top .ch-hero-prose,
.ch-hero-band-bottom .ch-hero-prose {
  max-width: 78ch;
}

/* Middle full-width translucent frosted glass band carrying the 3 interactive V8 figures */
.ch-hero-glass {
  position: relative;
  width: 100%;
  background: linear-gradient(180deg, rgba(16, 20, 28, 0.72) 0%, rgba(13, 16, 23, 0.80) 100%);
  backdrop-filter: blur(16px) saturate(1.3);
  -webkit-backdrop-filter: blur(16px) saturate(1.3);
  border-top: 1px solid rgba(200, 255, 46, 0.52);
  border-bottom: 1px solid rgba(200, 255, 46, 0.52);
  box-shadow:
    inset 0 1px 0 rgba(255, 255, 255, 0.16),
    inset 0 -1px 0 rgba(255, 255, 255, 0.08),
    0 22px 52px rgba(0, 0, 0, 0.44);
}

[data-theme='light'] .ch-hero-glass {
  background: linear-gradient(180deg, rgba(252, 253, 255, 0.78) 0%, rgba(246, 249, 253, 0.86) 100%);
  border-top: 1px solid rgba(76, 111, 0, 0.36);
  border-bottom: 1px solid rgba(76, 111, 0, 0.36);
  box-shadow:
    inset 0 1px 0 rgba(255, 255, 255, 0.95),
    inset 0 -1px 0 rgba(255, 255, 255, 0.75),
    0 18px 42px rgba(15, 23, 42, 0.12);
}

.ch-hero-glass-inner {
  max-width: 1380px;
  margin: 0 auto;
  padding: 18px 28px 22px;
  display: flex;
  flex-direction: column;
  gap: 14px;
}

.ch-hero-glass-bar {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 12px 20px;
  flex-wrap: wrap;
}

.ch-hero-glass-heading {
  display: flex;
  align-items: baseline;
  gap: 12px;
  flex-wrap: wrap;
}

.ch-hero-glass-kicker {
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.1em;
  color: var(--ch-accent-text);
}

.ch-hero-glass-sub { font-size: 13px; color: var(--ch-text-secondary); }

.ch-hero-glass-controls {
  display: flex;
  align-items: center;
  gap: 12px;
  flex-wrap: wrap;
}

.ch-hero-mode-seg {
  display: inline-flex;
  border: 1px solid var(--ch-border-strong);
  border-radius: 5px;
  overflow: hidden;
  background: rgba(10, 12, 16, 0.45);
}

[data-theme='light'] .ch-hero-mode-seg { background: rgba(255, 255, 255, 0.75); }

.ch-hero-mode-btn {
  appearance: none;
  border: 0;
  background: transparent;
  color: var(--ch-text-secondary);
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  padding: 5px 10px;
  cursor: pointer;
  transition: color 120ms ease, background-color 120ms ease;
}

.ch-hero-mode-btn[aria-pressed='true'] {
  background: var(--ch-accent);
  color: var(--ch-accent-ink);
  font-weight: 600;
}

.ch-hero-all-link {
  display: inline-flex;
  align-items: center;
  gap: 5px;
  font-family: var(--ch-font-mono);
  font-size: 12px;
  color: var(--ch-text-primary);
  text-decoration: none;
}

.ch-hero-all-link:hover { color: var(--ch-accent-text); }

.ch-hero-trio {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 16px;
  align-items: start;
}

.ch-hero-iso-card {
  border-radius: 10px;
  overflow: hidden;
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.24);
}

[data-theme='light'] .ch-hero-iso-card { box-shadow: 0 6px 18px rgba(15, 23, 42, 0.08); }

.ch-hero-iso-frame {
  display: block;
  width: 100%;
  height: 292px;
  border: 0;
  background: transparent;
}

.ch-h1 {
  margin: 0;
  font-family: var(--ch-font-display);
  font-size: clamp(2rem, 3.25vw, 2.9rem);
  font-weight: 700;
  line-height: 1.08;
  letter-spacing: -0.028em;
  text-wrap: balance;
  color: var(--ch-text-primary);
}

.ch-hero-prose {
  margin: 0;
  font-size: 15px;
  line-height: 1.65;
  color: var(--ch-text-secondary);
}

[data-theme='dark'] .ch-hero-prose { color: #d6ddea; }
[data-theme='light'] .ch-hero-prose { color: #1e293b; }

.ch-hero-prose strong { color: var(--ch-text-primary); font-weight: 700; }

.ch-hero-prose code {
  font-family: var(--ch-font-mono);
  font-size: 0.87em;
  padding: 1px 5px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 3px;
  color: var(--ch-text-primary);
}

.ch-hero-actions {
  display: flex;
  flex-wrap: wrap;
  gap: 12px;
  margin-top: 6px;
}

.ch-cta-primary,
.ch-cta-secondary {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  padding: 10px 18px;
  border-radius: 4px;
  font-size: 13.5px;
  font-weight: 600;
  text-decoration: none;
  transition: background-color 140ms ease, border-color 140ms ease, color 140ms ease;
}

.ch-cta-primary {
  background: var(--ch-accent);
  color: var(--ch-accent-ink);
  border: 1px solid var(--ch-accent);
}

.ch-cta-primary:hover {
  background: var(--ch-accent-hover);
  border-color: var(--ch-accent-hover);
}

.ch-cta-secondary {
  background: var(--ch-bg-card);
  color: var(--ch-text-primary);
  border: 1px solid var(--ch-border-strong);
}

.ch-cta-secondary:hover {
  background: var(--ch-bg-card-hover);
  border-color: var(--ch-accent);
}
```

### Hardware pillar strip — `site.css:546-626`

```css
.ch-hw-strip {
  position: relative;
  background-color: var(--ch-bg-canvas);
  border-bottom: 1px solid var(--ch-border-subtle);
  overflow: hidden;
}

/* Translucent drafter-grid texture, masked at top and bottom edges */
.ch-hw-strip::before {
  content: '';
  position: absolute;
  inset: 0;
  pointer-events: none;
  background-image:
    linear-gradient(to right, var(--ch-grid-line) 1px, transparent 1px),
    linear-gradient(to bottom, var(--ch-grid-line) 1px, transparent 1px);
  background-size: 28px 28px;
  -webkit-mask-image: linear-gradient(to bottom, transparent 0%, #000 18%, #000 82%, transparent 100%);
  mask-image: linear-gradient(to bottom, transparent 0%, #000 18%, #000 82%, transparent 100%);
}

.ch-hw-grid {
  position: relative;
  z-index: 1;
  max-width: 1380px;
  margin: 0 auto;
  padding: 0 28px;
  display: grid;
  grid-template-columns: repeat(4, minmax(0, 1fr));
}

.ch-hw-item {
  display: flex;
  align-items: center;
  gap: 14px;
  padding: 18px 18px 18px 14px;
  text-decoration: none;
  color: inherit;
  border-right: 1px solid var(--ch-border-subtle);
  transition: background-color 140ms ease;
}

.ch-hw-item:last-child { border-right: none; }

.ch-hw-item:hover { background: var(--ch-accent-dim); }

.ch-hw-item img {
  flex-shrink: 0;
  width: 78px;
  height: 78px;
  object-fit: contain;
  display: block;
  filter: drop-shadow(0 8px 14px rgba(0, 0, 0, 0.34));
}

[data-theme='light'] .ch-hw-item img {
  filter: drop-shadow(0 6px 12px rgba(15, 23, 42, 0.16));
}

.ch-hw-title {
  font-family: var(--ch-font-display);
  font-size: 14.5px;
  font-weight: 700;
  color: var(--ch-text-primary);
  line-height: 1.25;
}

.ch-hw-sub {
  margin-top: 3px;
  font-size: 12px;
  line-height: 1.45;
  color: var(--ch-text-muted);
}
```

### Scoreboard strip — `site.css:627-771`

```css
.ch-scoreboard-strip {
  background: var(--ch-bg-bar);
  border-bottom: 1px solid var(--ch-border-subtle);
  padding: 18px 28px;
}

.ch-scoreboard-inner {
  max-width: 1380px;
  margin: 0 auto;
  display: grid;
  grid-template-columns: minmax(0, 1fr) 356px;
  gap: 20px;
  align-items: stretch;
}
```

(metric-tile / digest-pill rules are in `components.md`.)

```css
.ch-load-error {
  padding: 12px 28px;
  font-size: 13.5px;
  font-weight: 500;
  background: var(--ch-status-fail-dim);
  border-bottom: 1px solid var(--ch-status-fail-bdr);
  color: var(--ch-text-primary);
}
```

### Spec container — `site.css:775-820`

```css
.ch-spec-container {
  max-width: 1380px;
  width: 100%;
  margin: 0 auto;
  padding: 40px 28px 80px;
  display: flex;
  flex-direction: column;
  gap: 64px;
  flex: 1 0 auto;
}

.ch-spec-row {
  display: grid;
  grid-template-columns: 440px minmax(0, 1fr);
  gap: 36px;
  align-items: start;
  padding-top: 44px;
  border-top: 1px solid var(--ch-border-subtle);
  scroll-margin-top: 70px;
}

.ch-spec-row:first-child {
  padding-top: 0;
  border-top: none;
}

.ch-spec-row-flush {
  padding-top: 0;
  border-top: none;
  align-items: center;
}

.ch-spec-row-sub {
  padding-top: 32px;
  border-top: 1px solid var(--ch-border-subtle);
}

.ch-prose-col,
.ch-artifact-col,
.ch-col {
  display: flex;
  flex-direction: column;
  gap: 16px;
  min-width: 0;
}
```

### Section lead + headings + prose — `site.css:821-968`

```css
.ch-section-lead {
  display: flex;
  align-items: center;
  gap: 16px;
}

.ch-flair-medallion {
  flex-shrink: 0;
  border-radius: 8px;
  border: 1px solid var(--ch-border-subtle);
  background: #191d27;
  object-fit: cover;
  display: block;
}

.ch-sticker-medallion {
  flex-shrink: 0;
  object-fit: contain;
  display: block;
  filter: drop-shadow(0 6px 12px rgba(0, 0, 0, 0.34));
}

[data-theme='light'] .ch-sticker-medallion {
  filter: drop-shadow(0 4px 10px rgba(15, 23, 42, 0.16));
}

.ch-flair-thumb {
  flex-shrink: 0;
  border-radius: 6px;
  border: 1px solid var(--ch-border-subtle);
  background: #191d27;
  object-fit: cover;
  display: block;
}

.ch-section-title {
  margin: 0;
  font-family: var(--ch-font-display);
  font-size: 25px;
  font-weight: 700;
  letter-spacing: -0.02em;
  line-height: 1.18;
  text-wrap: balance;
  color: var(--ch-text-primary);
}

.ch-subsection-title {
  margin: 0;
  font-family: var(--ch-font-display);
  font-size: 19px;
  font-weight: 700;
  letter-spacing: -0.015em;
  color: var(--ch-text-primary);
}

.ch-prose-text {
  margin: 0;
  font-size: 14.5px;
  line-height: 1.66;
  color: var(--ch-text-secondary);
}

.ch-prose-text strong { color: var(--ch-text-primary); font-weight: 600; }

.ch-prose-text code,
.ch-prose-note code,
.ch-fields code {
  font-family: var(--ch-font-mono);
  font-size: 0.88em;
  padding: 1px 5px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 3px;
  color: var(--ch-text-primary);
}

.ch-prose-note {
  margin: 0;
  font-size: 12.5px;
  line-height: 1.6;
  color: var(--ch-text-muted);
}

.ch-mono {
  font-family: var(--ch-font-mono);
  font-variant-numeric: tabular-nums;
}

.ch-mono-sm {
  font-family: var(--ch-font-mono);
  font-size: 12px;
  color: var(--ch-text-secondary);
}

.ch-nowrap { white-space: nowrap; }

.ch-muted { color: var(--ch-text-muted); font-size: 12px; }

.ch-accent-text { color: var(--ch-accent-text); }

.ch-status-dot {
  display: inline-block;
  width: 7px;
  height: 7px;
  border-radius: 50%;
  margin-right: 8px;
  vertical-align: middle;
  background: var(--ch-text-muted);
  flex-shrink: 0;
}

.ch-status-dot[data-tone='proved'] { background: var(--ch-status-proved); }
.ch-status-dot[data-tone='warn']   { background: var(--ch-status-warn); }
.ch-status-dot[data-tone='fail']   { background: var(--ch-status-fail); }

.ch-tone-label[data-tone='proved'], td[data-tone='proved'] { color: var(--ch-status-proved); }
.ch-tone-label[data-tone='warn'],   td[data-tone='warn']   { color: var(--ch-status-warn); }
.ch-tone-label[data-tone='fail'],   td[data-tone='fail']   { color: var(--ch-status-fail); }
```

### Provenance footer — `site.css:2261-2286`

```css
.ch-footer {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 14px;
  padding: 16px 28px;
  background: var(--ch-bg-bar);
  border-top: 1px solid var(--ch-border-subtle);
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  color: var(--ch-text-muted);
}

.ch-footer-left {
  display: inline-flex;
  align-items: center;
  gap: 10px;
  flex-wrap: wrap;
}

.ch-footer-mark {
  display: block;
  border-radius: 4px;
}
```

### Responsive — `site.css:2287-2420`

```css
@media (max-width: 1140px) {
  .ch-hero { padding: 32px 0 36px; }
  .ch-hero-trio { grid-template-columns: 1fr; max-width: 680px; }
  .ch-hw-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .ch-hw-item:nth-child(2n) { border-right: none; }
  .ch-hw-item:nth-child(-n + 2) { border-bottom: 1px solid var(--ch-border-subtle); }
  .ch-scoreboard-inner,
  .ch-spec-row,
  .ch-arch-split,
  .ch-two-col-equal { grid-template-columns: 1fr; }
  .ch-metrics-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .ch-digest-stack { flex-direction: row; flex-wrap: wrap; }
  .ch-digest-pill { flex: 1 1 240px; }
}

@media (max-width: 760px) {
  .ch-topbar {
    position: static;
    flex-wrap: wrap;
    padding: 10px 16px;
    gap: 8px 12px;
  }
  .ch-brand { order: 1; }
  .ch-topbar-right {
    order: 2;
    margin-left: auto;
    gap: 10px;
    font-size: 12px;
  }
  .ch-topbar-right .ch-nav-link { display: none; }
  .ch-theme-toggle { padding-left: 0; border-left: none; }
  .ch-nav {
    order: 3;
    width: 100%;
    flex-wrap: nowrap;
    overflow-x: auto;
    gap: 16px;
    padding-top: 6px;
    border-top: 1px solid var(--ch-border-subtle);
    -webkit-overflow-scrolling: touch;
  }
  .ch-nav a { white-space: nowrap; }
  .ch-hero { padding: 28px 0 32px; }
  .ch-hero-band-copy,
  .ch-hero-glass-inner { padding-left: 16px; padding-right: 16px; }
  .ch-hero-backdrop img { object-position: 66% center; }
  .ch-hw-grid { padding: 0 16px; grid-template-columns: 1fr; }
  .ch-hw-item {
    border-right: none;
    border-bottom: 1px solid var(--ch-border-subtle);
    padding: 14px 4px;
  }
  .ch-hw-item:last-child { border-bottom: none; }
  .ch-scoreboard-strip { padding: 14px 16px; }
  .ch-spec-container { padding: 28px 16px 56px; gap: 44px; }
  .ch-kernel-grid,
  .ch-renderers-grid,
  .ch-ingress-row { grid-template-columns: 1fr; }
  .ch-flow-arrow { justify-content: center; transform: rotate(90deg); }
  .ch-state-selector { grid-template-columns: 1fr; }
  .ch-code-row {
    grid-template-columns: 30px 20px 46px minmax(0, 1fr);
    padding: 2px 10px;
    font-size: 11.5px;
  }
  .ch-z3-inlay { margin-left: 10px; }
  .ch-ce-row { grid-template-columns: 36px minmax(0, 1fr); }
  .ch-ce-sort { display: none; }
  .ch-footer { padding: 14px 16px; }
}
```
