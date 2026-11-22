# CONDUIT Routes

There is **no router library**. The React site is a single-route SPA; navigation inside it is
anchor-based (`#coverage`, `#proofs`, `#scope`, `#arch`, `#ratchet`). The other surfaces are
standalone static HTML pages staged into `dist/` by `site/scripts/stage.mjs`.

Build: `npm --prefix site install && npm run build` → `vite build` → `dist/`, then `stage.mjs`
copies `data/`, `browser/ratchet.json`, `irrigation.html`, `irrigation.css`, `irrigation.js`,
`styles.css`, `v8-anatomy.html`, `v8-iso/pages/`, and `assets/` into `dist/`.

Deployment: GitHub Pages via `.github/workflows/pages.yml` (Node 20, typecheck + vite build + stage).

---

## Route map

| URL | Source | Layout | Notes |
|---|---|---|---|
| `/` | `site/src/main.tsx` → `site/src/App.tsx` | `site/src/App.tsx` shell | The whole product site. React 19 SPA, runtime data from `browser/ratchet.json` + `data/stats.json` |
| `/v8-anatomy.html` | `v8-anatomy.html` (repo root, 30 KB) | standalone | 8-figure V8 Tier-1 Mandatory Core isometric gallery. Self-contained `<style>` block + inline JS |
| `/irrigation.html` | `irrigation.html` (repo root) | standalone | Garden irrigation console. Links `styles.css` + `irrigation.css` + `irrigation.js` |
| `/v8-iso/pages/fig-01…fig-08.html` | `v8-iso/pages/*.html` | standalone | 8 isometric V8 figures, embedded as iframes in the hero |
| `/v8-iso/pages/showcase-01…03.html` | `v8-iso/pages/*.html` | standalone | 3 extra showcase figures (jet engine, sports car, cruise ship) |
| `/browser/ratchet.json` | `browser/ratchet.json` | — | Live ratchet telemetry, fetched at runtime |
| `/data/stats.json` | `data/stats.json` | — | Toolchain + host stats, fetched at runtime |

## Anchor targets inside `/`

| Anchor | Rendered by | Section title |
|---|---|---|
| `#top` | `App.tsx:114` (`id="top"` on `.ch-page-shell`) | — |
| `#coverage` | `SectionCoverage.tsx:46` | "Twenty real Chrome zero-days, mapped to our architecture" |
| `#proofs` | `SectionVerus.tsx:141` | "Tests check examples. Proofs check every input." |
| `#scope` | `SectionWhy.tsx:46` | "Why nobody verifies all of Linux—or all of Chrome" |
| `#arch` | `App.tsx:390` | "One proved kernel in front of disposable renderers" |
| `#ratchet` | `SectionStatus.tsx:35` | "Live proof status—and what is still unbuilt" |

Anchor scroll offset is handled by `scroll-margin-top: 70px` on `.ch-spec-row` / `.ch-arch-section`
/ `.ch-status-section`, accounting for the sticky 54px topbar.

---

## IMPORTANT: two distinct visual systems

The repo contains **two separate design languages**. Any design work must pick one and say so.

### System A — the main site (`site/`)

- Chartreuse accent `#c8ff2e` on obsidian-slate `#0e1015` (dark) / drafting paper `#f6f8fb` (light)
- Archivo / Manrope / JetBrains Mono, self-hosted
- Dense "executable specification" register: hairline 1px borders, 4px radii, mono micro-labels,
  tabular numerals, 4-state tone system
- Toggleable dark/light via `data-theme` on `<html>`, persisted to `localStorage['conduit-theme']`
- Token prefix: `--ch-*`

### System B — the standalone demo pages (`irrigation.html`, `styles.css`, `irrigation.css`)

- Legacy stylesheet, blue/violet palette: `--bg: #070b16`, `--panel: #0d1424`, `--line: #1d2a44`,
  `--text: #e6edf7`, `--muted: #8ea0bf`, `--accent: #4dd4ff` (cyan), `--accent2: #8f7bff` (violet)
- System font stack (no Archivo/Manrope), 6vw gutters, `border-radius: 999px` pills
- **Dark only — no light theme, no tone system, no `data-theme`**
- `styles.css` is also the base for the old root landing page and is still shipped in `dist/`

`v8-anatomy.html` and `v8-iso/pages/*` are a third, lighter case: they declare `data-theme="dark"`
and load the **same self-hosted fonts**, but carry their own inline styles rather than `--ch-*`.

---

## No router config

There is no `router/index.ts`, `routes.ts`, or equivalent to include. `site/src/main.tsx` is:

```tsx
import { createRoot } from 'react-dom/client';
import './site.css';
import App from './App';

createRoot(document.getElementById('root')!).render(<App />);
```

`site/vite.config.ts` is a plain Vite + React plugin config with `base: './'`-style relative asset
handling for GitHub Pages; it does not define routes.
