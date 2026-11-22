# CONDUIT Design Tokens & Theme

Source of truth: `site/src/site.css` (2420 lines) + `site/index.html` (font faces).
No Tailwind, no CSS-in-JS for the app's own layer. `@clickhouse/click-ui` (styled-components) is
used only for a few controls (`Switch`, `Badge`, `Button`) — everything else is hand-written CSS
with a `ch-` BEM-ish prefix and CSS custom properties.

---

## PART 1 — Compact token summary (budget-friendly; pass this, not all of site.css)

### Product context

- **Product**: CONDUIT Lab — a browser engine whose security-critical components are proved in
  Rust with Verus + Z3. The site is an *executable specification* + *live ratchet telemetry*.
- **Audience**: security engineers, browser-engine developers, formal-methods researchers, and
  funding-minded readers. Primary job-to-be-done: *convince a skeptic that the security claims are
  real and machine-checked*.
- **Voice**: precise, evidence-first, anti-hype. Numbers are never hand-typed — every metric loads
  at runtime from `browser/ratchet.json` and `data/stats.json`. Missing data renders the literal
  string `not recorded` (never a stale placeholder).
- **Layout archetype**: Tufte-style two-column executable specification — a narrow prose column
  (440px) beside a wide artifact column, so code/proofs/diagrams sit beside the claim they prove.

### Color — dark theme (default) `:root, [data-theme='dark']`

| Token | Value | Use |
|---|---|---|
| `--ch-bg-canvas` | `#0e1015` | page background (obsidian-slate) |
| `--ch-bg-bar` | `#14171f` | topbar, table headers, footer, DAG bar |
| `--ch-bg-card` | `#191d27` | cards, panels, code headers |
| `--ch-bg-card-hover` | `#212735` | hover states |
| `--ch-bg-code` | `#0a0c10` | code workbench, DAG canvas, contract boxes |
| `--ch-grid-line` | `rgba(255, 255, 255, 0.055)` | background grid lines |
| `--ch-border-subtle` | `#262c3a` | default 1px borders, dividers |
| `--ch-border-strong` | `#394256` | emphasized borders, selected nodes |
| `--ch-text-primary` | `#f4f6fa` | headings, key values |
| `--ch-text-secondary` | `#bcc4d4` | body prose |
| `--ch-text-muted` | `#8a94a8` | labels, captions, metadata |
| `--ch-accent` | `#c8ff2e` | chartreuse — primary brand accent, bars, focus ring |
| `--ch-accent-text` | `#c8ff2e` | accent-colored text (dark) |
| `--ch-accent-hover` | `#d8ff5e` | accent hover |
| `--ch-accent-ink` | `#0a1202` | text *on* accent fill (near-black green) |
| `--ch-accent-dim` | `rgba(200, 255, 46, 0.09)` | accent-tinted surface |
| `--ch-accent-bdr` | `rgba(200, 255, 46, 0.38)` | accent-tinted border |
| `--ch-status-proved` | `#34d399` | emerald — PROVED / verified state |
| `--ch-status-proved-dim` | `rgba(52, 211, 153, 0.10)` | proved surface |
| `--ch-status-proved-bdr` | `rgba(52, 211, 153, 0.36)` | proved border |
| `--ch-status-fail` | `#fb7185` | rose — FAILED / trust violation |
| `--ch-status-fail-dim` | `rgba(251, 113, 133, 0.11)` | fail surface |
| `--ch-status-fail-bdr` | `rgba(251, 113, 133, 0.38)` | fail border |
| `--ch-status-warn` | `#fb923c` | orange — WARN / untrusted / pending |
| `--ch-status-warn-dim` | `rgba(251, 146, 60, 0.10)` | warn surface |
| `--ch-status-warn-bdr` | `rgba(251, 146, 60, 0.38)` | warn border |
| `--ch-shadow-card` | `0 10px 28px rgba(0, 0, 0, 0.34)` | card shadow |

### Color — light theme `[data-theme='light']`

| Token | Value |
|---|---|
| `--ch-bg-canvas` | `#f6f8fb` (drafting paper) |
| `--ch-bg-bar` | `#edf1f7` |
| `--ch-bg-card` | `#ffffff` |
| `--ch-bg-card-hover` | `#f2f5fa` |
| `--ch-bg-code` | `#f0f3f8` |
| `--ch-grid-line` | `rgba(15, 23, 42, 0.065)` |
| `--ch-border-subtle` | `#d5dce6` |
| `--ch-border-strong` | `#aeb9ca` |
| `--ch-text-primary` | `#0f172a` |
| `--ch-text-secondary` | `#334155` |
| `--ch-text-muted` | `#56657c` |
| `--ch-accent` | `#b8f500` (vivid chartreuse fill) |
| `--ch-accent-text` | `#3f6b09` (dark olive ink for accent text) |
| `--ch-accent-hover` | `#a6de00` |
| `--ch-accent-ink` | `#0a1202` |
| `--ch-accent-dim` | `rgba(163, 230, 53, 0.16)` |
| `--ch-accent-bdr` | `rgba(77, 124, 15, 0.42)` |
| `--ch-status-proved` | `#047857` |
| `--ch-status-proved-dim` | `rgba(4, 120, 87, 0.08)` |
| `--ch-status-proved-bdr` | `rgba(4, 120, 87, 0.34)` |
| `--ch-status-fail` | `#be123c` |
| `--ch-status-fail-dim` | `rgba(190, 18, 60, 0.08)` |
| `--ch-status-fail-bdr` | `rgba(190, 18, 60, 0.34)` |
| `--ch-status-warn` | `#c2410c` |
| `--ch-status-warn-dim` | `rgba(234, 88, 12, 0.07)` |
| `--ch-status-warn-bdr` | `rgba(234, 88, 12, 0.34)` |
| `--ch-shadow-card` | `0 8px 20px rgba(15, 23, 42, 0.07)` |

### Semantic tone system (the single most important pattern)

A four-value tone drives color across every status-bearing element, always via a `data-tone`
attribute: **`proved` | `warn` | `fail` | `neutral`**.

- `proved` → `--ch-status-proved` (emerald)
- `warn` → `--ch-status-warn` (orange) — also "untrusted / pending"
- `fail` → `--ch-status-fail` (rose) — also "trusted shortcut / unsafe"
- `neutral` → `--ch-text-muted`

Tone is applied to: stat tiles, status dots, tally items, accordion rows, state buttons, verified
strips, code rows, Z3 inlays, badges, scale bars, DAG nodes/edges, table cells, tone labels.

### Typography

| Role | Family | Notes |
|---|---|---|
| Display / headings | **Archivo** (variable 400–800, self-hosted woff2) | `--ch-font-display`; h1, `.ch-section-title`, `.ch-subsection-title`, block headings |
| Body / UI | **Manrope** (variable 400–700, self-hosted woff2) | `--ch-font-sans`; body copy, labels, buttons |
| Code / data / numeric | **JetBrains Mono** (variable 400–700, self-hosted woff2) | `--ch-font-mono`; all numbers, IDs, hashes, code, table headers, badges |

Type scale (approximate, from site.css):

| Token class | Size | Weight | Family |
|---|---|---|---|
| `.ch-h1` | `clamp(2rem, 3.25vw, 2.9rem)` → 32–46px | 700 | display |
| `.ch-section-title` | 25px | 700 | display |
| `.ch-subsection-title` | 19px | 700 | display |
| `.ch-block-head h3` | 17px | 700 | display |
| `.ch-hw-title` | 14.5px | 700 | display |
| body | 15px / 1.62 | 400 | sans |
| `.ch-hero-prose` | 15px / 1.65 | 400 | sans |
| `.ch-prose-text` | 14.5px / 1.66 | 400 | sans |
| `.ch-prose-note` | 12.5px | 400 | sans |
| `.ch-metric-value` | 24px | 700 | mono, tabular-nums |
| `.ch-det-summary` | 13.5px | 500 | sans |
| `.ch-table` | 13px | 400 | sans |
| `.ch-code-row` | 12.5px / 23px | 400 | mono |
| `.ch-mono-sm` | 12px | 400 | mono |
| `.ch-mono-link` | 12px | 600 | mono |
| `.ch-metric-label` / `.ch-inlay-badge` | 10.5px | 600–700 | mono, uppercase, `letter-spacing .06em` |
| micro-label (dt, table th) | 10.5px | 600 | mono, uppercase, `letter-spacing .06em` |

Numerals use `font-variant-numeric: tabular-nums` everywhere (`.ch-mono`, `.ch-num`,
`.ch-scale-label strong`).

### Spacing

No spacing scale token exists — spacing is literal px in the CSS. Observed rhythm:

- xs 4px · sm 8px · md 12px · lg 16px · xl 24px · 2xl 28px · 3xl 36px · 4xl 44px · 5xl 64px
- Page gutter: `28px` desktop / `16px` ≤760px
- Topbar padding: `8px 28px` (desktop) → `10px 16px` (≤760px)
- Card padding: `12px 14px` (small) · `14px 16px` (medium) · `16px 18px` (large)
- Section gap inside `.ch-spec-container`: `64px` → `44px` ≤760px
- `.ch-spec-row` grid gap `36px`, padding-top `44px`

### Radii

- `3px` — pills, lane pills, inlay badges, scale track, CE table
- `4px` — cards, tiles, buttons, tables, accordion rows, detail cards (the default)
- `5px` — DAG wrap, kernel shell, honesty/disclosure cards
- `6px` — iso frame, arch diagram
- `8px` — flair medallion
- `50%` — status dots (7px circle)

### Shadows

- `--ch-shadow-card`: `0 10px 28px rgba(0,0,0,.34)` (dark) / `0 8px 20px rgba(15,23,42,.07)` (light)
- `.ch-sticker-medallion`: `drop-shadow(0 6px 12px rgba(0,0,0,.34))` / light `drop-shadow(0 4px 10px rgba(15,23,42,.16))`

### Grid & layout

- Content max width: `.ch-spec-container` → `1380px`
- Tufte spec row: `grid-template-columns: 440px minmax(0, 1fr)` (collapses to 1fr ≤1140px)
- Arch split: `minmax(0,5fr) minmax(0,7fr)` (collapses ≤1140px)
- Hero trio: 3 equal columns (1fr ≤1140px)
- Metrics grid: 4 equal columns (2 ≤1140px)

### Breakpoints

- `max-width: 1140px` — hero trio, hw grid, scoreboard, spec row, arch split, two-col all collapse
- `max-width: 760px` — topbar becomes static/wrapped, nav scrolls horizontally, code rows
  re-grid, footer stacks

### Motion

- 120ms `ease` — hover transitions on color/border/background (nav links, buttons, tiles)
- 140ms `ease` — accordion chevron rotate 90deg, DAG edge stroke/opacity, DAG node opacity
- No keyframe animations anywhere. Motion is limited to state feedback and disclosure.
- `html { scroll-behavior: smooth; }`; `scroll-margin-top: 70px` on anchored sections.

### Focus & selection

- `:focus-visible` → `outline: 2px solid var(--ch-accent); outline-offset: 2px`
- `::selection` → accent background with `--ch-accent-ink` text

### Glass band (signature hero effect)

```
linear-gradient(90deg,
  rgba(200,255,46,0) 0%,
  rgba(255,255,255,0.07) 25%,
  rgba(200,255,46,0.10) 50%,
  rgba(255,255,255,0.07) 75%,
  rgba(200,255,46,0) 100%)
```
Light variant swaps in `rgba(163,230,53,0)` / `rgba(255,255,255,0.82)` / `rgba(184,245,0,0.18)`.

---

## PART 2 — Raw source dumps

### 2a. Complete token block — `site/src/site.css:1-135`

```css
/* CONDUIT Verified Browser Engine — Executable Specification & Live Ratchet
 * Dark: obsidian-slate + chartreuse (#c8ff2e) + emerald (#34d399) + rose (#fb7185).
 * Light: drafting paper + vivid chartreuse (#b8f500 CTA / #4d7c0f ink) + emerald + crimson.
 * Self-hosted Archivo (display), Manrope (body), JetBrains Mono (code/data).
 */

:root,
[data-theme='dark'] {
  --ch-bg-canvas: #0e1015;
  --ch-bg-bar: #14171f;
  --ch-bg-card: #191d27;
  --ch-bg-card-hover: #212735;
  --ch-bg-code: #0a0c10;
  --ch-grid-line: rgba(255, 255, 255, 0.055);
  --ch-glass-band: linear-gradient(
    90deg,
    rgba(200, 255, 46, 0) 0%,
    rgba(255, 255, 255, 0.07) 25%,
    rgba(200, 255, 46, 0.10) 50%,
    rgba(255, 255, 255, 0.07) 75%,
    rgba(200, 255, 46, 0) 100%
  );
  --ch-border-subtle: #262c3a;
  --ch-border-strong: #394256;
  --ch-text-primary: #f4f6fa;
  --ch-text-secondary: #bcc4d4;
  --ch-text-muted: #8a94a8;
  --ch-accent: #c8ff2e;
  --ch-accent-text: #c8ff2e;
  --ch-accent-hover: #d8ff5e;
  --ch-accent-ink: #0a1202;
  --ch-accent-dim: rgba(200, 255, 46, 0.09);
  --ch-accent-bdr: rgba(200, 255, 46, 0.38);
  --ch-status-proved: #34d399;
  --ch-status-proved-dim: rgba(52, 211, 153, 0.10);
  --ch-status-proved-bdr: rgba(52, 211, 153, 0.36);
  --ch-status-fail: #fb7185;
  --ch-status-fail-dim: rgba(251, 113, 133, 0.11);
  --ch-status-fail-bdr: rgba(251, 113, 133, 0.38);
  --ch-status-warn: #fb923c;
  --ch-status-warn-dim: rgba(251, 146, 60, 0.10);
  --ch-status-warn-bdr: rgba(251, 146, 60, 0.38);
  --ch-shadow-card: 0 10px 28px rgba(0, 0, 0, 0.34);
  --ch-font-display: 'Archivo', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  --ch-font-sans: 'Manrope', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  --ch-font-mono: 'JetBrains Mono', ui-monospace, SFMono-Regular, Menlo, monospace;
}

[data-theme='light'] {
  --ch-bg-canvas: #f6f8fb;
  --ch-bg-bar: #edf1f7;
  --ch-bg-card: #ffffff;
  --ch-bg-card-hover: #f2f5fa;
  --ch-bg-code: #f0f3f8;
  --ch-grid-line: rgba(15, 23, 42, 0.065);
  --ch-glass-band: linear-gradient(
    90deg,
    rgba(163, 230, 53, 0) 0%,
    rgba(255, 255, 255, 0.82) 25%,
    rgba(184, 245, 0, 0.18) 50%,
    rgba(255, 255, 255, 0.82) 75%,
    rgba(163, 230, 53, 0) 100%
  );
  --ch-border-subtle: #d5dce6;
  --ch-border-strong: #aeb9ca;
  --ch-text-primary: #0f172a;
  --ch-text-secondary: #334155;
  --ch-text-muted: #56657c;
  --ch-accent: #b8f500;
  --ch-accent-text: #3f6b09;
  --ch-accent-hover: #a6de00;
  --ch-accent-ink: #0a1202;
  --ch-accent-dim: rgba(163, 230, 53, 0.16);
  --ch-accent-bdr: rgba(77, 124, 15, 0.42);
  --ch-status-proved: #047857;
  --ch-status-proved-dim: rgba(4, 120, 87, 0.08);
  --ch-status-proved-bdr: rgba(4, 120, 87, 0.34);
  --ch-status-fail: #be123c;
  --ch-status-fail-dim: rgba(190, 18, 60, 0.08);
  --ch-status-fail-bdr: rgba(190, 18, 60, 0.34);
  --ch-status-warn: #c2410c;
  --ch-status-warn-dim: rgba(234, 88, 12, 0.07);
  --ch-status-warn-bdr: rgba(234, 88, 12, 0.34);
  --ch-shadow-card: 0 8px 20px rgba(15, 23, 42, 0.07);
}

*,
*::before,
*::after {
  box-sizing: border-box;
}

html {
  scroll-behavior: smooth;
  color-scheme: dark;
}

html[data-theme='light'] {
  color-scheme: light;
}

body {
  margin: 0;
  background: var(--ch-bg-canvas);
  color: var(--ch-text-primary);
  font-family: var(--ch-font-sans);
  font-size: 15px;
  line-height: 1.62;
  -webkit-font-smoothing: antialiased;
}

::selection {
  background: var(--ch-accent);
  color: var(--ch-accent-ink);
}

:focus-visible {
  outline: 2px solid var(--ch-accent);
  outline-offset: 2px;
}
```

### 2b. Font faces — `site/index.html:13-62`

Self-hosted variable woff2, `font-display: swap`, latin + latin-ext subsets, declared in the HTML
head (not in CSS) so they load before the bundle.

```html
<style>
  @font-face { font-family: "Archivo"; font-style: normal; font-weight: 400 800; font-display: swap;
    src: url("assets/fonts/archivo-latin-ext.woff2") format("woff2");
    unicode-range: U+0100-02BA, U+02BD-02C5, U+02C7-02CC, U+02CE-02D7, U+02DD-02FF, U+0304, U+0308, U+0329, U+1D00-1DBF, U+1E00-1E9F, U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113, U+2C60-2C7F, U+A720-A7FF; }
  @font-face { font-family: "Archivo"; font-style: normal; font-weight: 400 800; font-display: swap;
    src: url("assets/fonts/archivo-latin.woff2") format("woff2");
    unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD; }
  @font-face { font-family: "Manrope"; font-style: normal; font-weight: 400 700; font-display: swap;
    src: url("assets/fonts/manrope-latin-ext.woff2") format("woff2");
    unicode-range: U+0100-02BA, U+02BD-02C5, U+02C7-02CC, U+02CE-02D7, U+02DD-02FF, U+0304, U+0308, U+0329, U+1D00-1DBF, U+1E00-1E9F, U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113, U+2C60-2C7F, U+A720-A7FF; }
  @font-face { font-family: "Manrope"; font-style: normal; font-weight: 400 700; font-display: swap;
    src: url("assets/fonts/manrope-latin.woff2") format("woff2");
    unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD; }
  @font-face { font-family: "JetBrains Mono"; font-style: normal; font-weight: 400 700; font-display: swap;
    src: url("assets/fonts/jetbrains-mono-latin-ext.woff2") format("woff2");
    unicode-range: U+0100-02BA, U+02BD-02C5, U+02C7-02CC, U+02CE-02D7, U+02DD-02FF, U+0304, U+0308, U+0329, U+1D00-1DBF, U+1E00-1E9F, U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113, U+2C60-2C7F, U+A720-A7FF; }
  @font-face { font-family: "JetBrains Mono"; font-style: normal; font-weight: 400 700; font-display: swap;
    src: url("assets/fonts/jetbrains-mono-latin.woff2") format("woff2");
    unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD; }
</style>
```

### 2c. `site/src/site.css` — section index (for targeted `--context-file` line ranges)

The file is 2420 lines — **do not pass it whole**. Use these ranges:

| Lines | Content |
|---|---|
| 1-135 | tokens + reset + base (see 2a) |
| 136-235 | page shell + topbar / brand / nav / theme toggle |
| 236-545 | hero: backdrop, stack, glass band, trio, h1, prose, CTAs |
| 546-626 | hardware pillar strip |
| 627-771 | scoreboard strip, metric tiles, digest pills, load error |
| 772-968 | Tufte spec layout, section lead, headings, prose, status dot, tone labels |
| 969-1100 | CVE tally, detail card, filter bar |
| 1101-1498 | Verus 4-state workbench, code workbench, Z3 inlay, CE table, proof picker |
| 1499-1679 | log-scale bars, accordion rows, definition fields |
| 1680-1873 | architecture plate + trust-boundary diagram |
| 1874-2016 | honesty card, blocks, benchmarks, contract box |
| 2017-2124 | data tables |
| 2125-2257 | proof dependency DAG |
| 2258-2286 | provenance footer |
| 2287-2420 | responsive breakpoints (1140px, 760px) |

### 2d. Theme switching mechanism — `site/src/App.tsx:47-59`

```tsx
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
```

Dark is the default. The attribute `data-theme` is set on `<html>`; all theme switching is CSS-only
via `[data-theme='light']` overrides of the same `--ch-*` custom properties. The theme is also
broadcast into the hero iframes via `postMessage`.

### 2e. External library

`@clickhouse/click-ui` v0.16 (styled-components 6). Used for `ClickUIProvider` (theme context,
wraps the whole app), `Switch` (theme toggle), `Badge` (status chips in SectionVerus/SectionStatus/
SectionCoverage), `Button` (SectionVerus). It is *not* the visual language of the app — the
hand-written `--ch-*` layer overrides its presence. Do not introduce additional Click UI components
into new work without checking against the tokens above.
