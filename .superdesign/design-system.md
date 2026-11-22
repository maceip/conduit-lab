# CONDUIT Design System

The reusable design system for CONDUIT Lab — a formally verified browser engine built in Rust with
Verus + Z3. This document is the constraint set for every design draft and every new surface.

> **Scope.** This system codifies the design language that already ships in this repo, across
> **all** surfaces: the React specification site, the V8 anatomy gallery, the isometric figure
> pages, and the legacy irrigation console. It is the single source of truth for *new* work —
> new pages, new components, and any future consolidation of these surfaces should match these
> rules rather than invent new ones.

---

## 1. Product context

**What CONDUIT is.** A browser engine whose security-critical components are machine-checked
against their published standards by a theorem prover. Eleven Rust crates (`vurl`, `vjs_spec`,
`vjs_types`, `vjs_object`, `vjs_syntax`, `vjs`, `vjs_webidl`, `vjs_builtins`, `vjs_gc`, `vjs_vm`,
`vwasm`) are `#![forbid(unsafe_code)]` with zero `assume` / `admit` / `external_body` / `unsafe`.
Every unproved line is counted as *trusted*, and that count is ratcheted so it never rises.

**Who it is for.** Security engineers, browser-engine developers, formal-methods researchers, and
prospective contributors or funders. The reader is technically literate and skeptical.

**Job to be done.** *"Convince me this security claim is real and machine-checked, and show me
exactly which part of the system is still unproven."*

**Voice.** Precise, evidence-first, anti-hype. Short declarative sentences. Never overclaim —
when something is not verified, say so plainly and label it untrusted. The pattern is always
*claim → mechanism → evidence → honest limit*.

**What success looks like.** A reader leaves believing (a) the proofs are real, (b) the
architecture isolates what isn't proved yet, and (c) the project knows its own limits.

---

## 2. Surfaces & the three-family taxonomy

The repo contains **three visual families**. They share a philosophy but not a palette. Any new
work must declare which family it belongs to.

| Family | Name | Surfaces | Accent | Themes |
|---|---|---|---|---|
| **A** | **CONDUIT Core** | `site/` (the spec site), `v8-anatomy.html` (gallery) | chartreuse `#c8ff2e` | dark + light |
| **B** | **CAD Neutral** | `v8-iso/pages/fig-*.html` (11 isometric figures) | **none — pure grayscale** | dark + light |
| **C** | **Legacy Demo** | `irrigation.html` + `styles.css` + `irrigation.css` | cyan `#4dd4ff` + violet `#8f7bff` | dark only |

**Family A and B are the current house style.** Family C is a legacy subsystem retained for the
irrigation demo; extend it consistently if you touch it, but new product surfaces belong to A.

### The five spec sections (Family A, all Tufte two-column rows)

1. `#coverage` — Twenty real Chrome zero-days, mapped to our architecture
2. `#proofs` — Tests check examples. Proofs check every input. (Verus 4-state workbench)
3. `#scope` — Why nobody verifies all of Linux—or all of Chrome
4. `#arch` — One proved kernel in front of disposable renderers
5. `#ratchet` — Live proof status—and what is still unbuilt

**Document order inside a section is always:** section lead (medallion + title) → prose claim →
artifact/evidence → honest caveat or source note.

---

## 3. Key features the system must serve

- **Live telemetry.** Metrics load at runtime from `browser/ratchet.json` and `data/stats.json`.
  Never hard-code a number that a script can supply.
- **Honest failure.** When data is missing, show the literal string `not recorded` — never a
  stale placeholder, never a zero, never a blank. Every family does this.
- **Status legibility.** Every claim carries a state: proved / warn / fail / neutral. A reader
  must be able to scan a page and know what is verified.
- **Trust boundary made visible.** Verified code and unverified code must look different, always.
- **Provenance.** Where a number came from is as important as the number: source links, digests,
  timestamps, and the exact upstream standard commit.

---

# FAMILY A — CONDUIT Core

> Covers `site/` and `v8-anatomy.html`. This is the primary family.

## A1. Color

Two themes, driven by `data-theme` on `<html>`. Dark is the default; light is selected by the
topbar switch and persisted to `localStorage['conduit-theme']`. **Both families A and the gallery
share the same `conduit-theme` key**, so the toggle stays in sync across pages.

**Dark (default) — obsidian-slate + chartreuse.** `site/src/site.css` tokens:

| Role | Token | Value |
|---|---|---|
| Canvas | `--ch-bg-canvas` | `#0e1015` |
| Bar | `--ch-bg-bar` | `#14171f` |
| Card | `--ch-bg-card` | `#191d27` |
| Card hover | `--ch-bg-card-hover` | `#212735` |
| Code surface | `--ch-bg-code` | `#0a0c10` |
| Border | `--ch-border-subtle` / `--ch-border-strong` | `#262c3a` / `#394256` |
| Text | primary / secondary / muted | `#f4f6fa` / `#bcc4d4` / `#8a94a8` |
| **Accent** | `--ch-accent` | **`#c8ff2e`** (chartreuse) |
| Accent ink (on accent fill) | `--ch-accent-ink` | `#0a1202` |
| Proved | `--ch-status-proved` | `#34d399` (emerald) |
| Fail | `--ch-status-fail` | `#fb7185` (rose) |
| Warn | `--ch-status-warn` | `#fb923c` (orange) |

**Light — drafting paper.** Canvas `#f6f8fb` · bar `#edf1f7` · card `#ffffff` · code `#f0f3f8` ·
border `#d5dce6` / `#aeb9ca` · text `#0f172a` / `#334155` / `#56657c` · accent `#b8f500` with
accent text `#3f6b09` (dark olive ink — **never** bright chartreuse for text on light) · proved
`#047857` · fail `#be123c` · warn `#c2410c`.

The gallery (`v8-anatomy.html`) uses its own token names but the **same family**: `--bg #0c0e13` ·
`--bg-elev #12161f` · `--bg-card #151922` · `--border #252b38` / `--border-strong #363f52` ·
`--text #eef2f8` / `--text-sec #a6b0c3` / `--text-muted #707b90` · **`--accent #c8ff2e`** ·
`--proved #3dd68c`; light theme `--bg #f4f5f7` · `--accent #4c6f00` · `--proved #0f7b49`.

**Accent rule.** Chartreuse is the single brand accent of Family A. Used for: primary CTA fills,
the hero glass band's top/bottom hairlines, focus rings, selection, active-tab borders, mono key
labels, scale-bar fills, gallery `seg-btn` active state. It is **never** used for body text on
light, never for large backgrounds, and never as a gradient between two hues.

**The four-state tone system.** The single most important pattern in Family A. Every
status-bearing element carries a `data-tone` attribute with one of four values:

| Tone | Meaning | Color |
|---|---|---|
| `proved` | Machine-checked, verified | `--ch-status-proved` |
| `warn` | Untrusted, pending, unverified surface | `--ch-status-warn` |
| `fail` | Violated, a trusted shortcut, an error | `--ch-status-fail` |
| `neutral` | No claim / unknown | `--ch-text-muted` |

Each tone has a `-dim` surface value and a `-bdr` border value. Tones appear on: stat tiles,
status dots, tally items, accordion rows, state buttons, verified strips, code rows, Z3 inlays,
badges, scale bars, DAG nodes and edges, table cells, and tone labels.

**Never introduce a fifth tone, a new hue family, or a gradient palette.** If something needs a
new state, map it onto one of the four.

## A2. Typography

Three self-hosted variable fonts, declared via `@font-face` in `site/index.html` (and inlined in
`v8-anatomy.html`):

| Role | Family | Weights | CSS var |
|---|---|---|---|
| Display — headings, titles | **Archivo** | 400–800 | `--ch-font-display` |
| Body — prose, UI, buttons | **Manrope** | 400–700 | `--ch-font-sans` |
| Code & data — numbers, IDs, hashes | **JetBrains Mono** | 400–700 | `--ch-font-mono` |

Scale: h1 `clamp(2rem, 3.25vw, 2.9rem)` / 700 · section title 25px / 700 · subsection title
19px / 700 · block title 17px / 700 · gallery h1 `clamp(1.85rem, 3vw, 2.55rem)` · gallery machine
title `1.25rem` / gallery section head `1.45rem` · body 15px / 1.62 · prose 14.5px / 1.66 ·
metric value 24px mono / 700 · detail row 13.5px / 500 · table 13px · code row 12.5px / 23px ·
micro-label 10.5px mono uppercase `letter-spacing .06em`.

Rules:
- **All numbers are tabular.** `font-variant-numeric: tabular-nums` on every metric, count, hash,
  duration, and table numeric cell.
- **Mono for anything a machine produced** — identifiers, file paths, CVE ids, digests, versions,
  line numbers, code, and (in the gallery) jump-nav links and counterpart pills. Sans for human
  prose. Never mix.
- Micro-labels (table heads, `dt` terms, tile labels, tier headings, gallery eyebrows) are
  **mono, uppercase, 10.5–12px, `letter-spacing .06–.1em`** — the "technical instrument" texture.
- Never introduce a serif, a decorative face, or a fourth family.

## A3. Spacing

Literal pixel spacing, no scale tokens, but a consistent rhythm: 4 · 8 · 12 · 16 · 20 · 24 · 28 ·
36 · 44 · 64. Page gutter 28px (16px ≤760px). Section gap 64px (44px mobile). Card padding 12×14,
14×16, or 16×18. Gallery container 1420px wide with 36/28/80 padding.

Do not invent values between the steps.

## A4. Radii, borders, shadows

Radii 3px (pills/badges) · **4px (cards, buttons, tables — the default)** · 5px (DAG wrap, kernel
shell) · 6px (iso frame, arch diagram, gallery machine cards, seg-groups) · 8px (medallion) ·
10px (hero iso card, gallery ratchet box) · 14px (gallery machine card) · 50% (status dots).

Borders are **1px hairline** `--ch-border-subtle` (default) or `--ch-border-strong` (emphasis).
No 2px borders, no double borders. Shadows are rare and deep: only `--ch-shadow-card`
(`0 10px 28px rgba(0,0,0,.34)`) and the medallion `drop-shadow`.

## A5. Layout structure

- Content max width **1380px** (site) / **1420px** (gallery), centred. Page gutter 28px.
- **Tufte two-column spec rows**: `grid-template-columns: 440px minmax(0, 1fr)`, gap 36px.
  Prose column 440px fixed, artifact column flexible. This is the signature layout.
- Architecture split: `minmax(0,5fr) minmax(0,7fr)`.
- Gallery intro split: `minmax(0,1.45fr) minmax(0,1fr)`. Gallery grids: 2-up machines, 3-up showcases.
- Topbar: sticky, 54px min-height (site) / `z-index: 30`; gallery topbar `z-index: 40`,
  `backdrop-filter: blur(12px)` over `color-mix(in srgb, var(--bg-elev) 88%, transparent)`.
- Anchored sections get `scroll-margin-top: 70px` to clear the sticky bar.
- Breakpoints — site: **1140px** (grids collapse to 1–2 columns) and **760px** (topbar unwraps,
  nav scrolls horizontally, code rows re-grid, footer stacks). Gallery: **1040px** (intro and both
  grids collapse to 1 column).

## A6. Motion

There are **no keyframe animations** in Family A. Motion is limited to:

| Duration | Easing | Applies to |
|---|---|---|
| 120ms | `ease` | Colour / border / background hover feedback |
| 140ms | `ease` | Accordion chevron rotate 90°, DAG edge stroke & opacity, CTA transitions |

Plus `scroll-behavior: smooth` on `html`. Never add entrance animations, parallax, looping motion,
or animated gradients. The register is *instrument, not toy*.

## A7. Iconography

Eight hand-drawn 16×16 stroked icons (`site/src/icons.tsx`): Check, X, Clock, ShieldAlert, Copy,
External, Chevron, ArrowDown, ArrowRight. `fill: none`, `stroke: currentColor`, `stroke-width: 1.6`,
round caps and joins, default size 14px. Icons inherit `currentColor` so they take their
container's tone. **Reproduce these 1:1 — do not substitute generic glyphs or an icon font.**

---

# FAMILY B — CAD Neutral

> Covers the 11 isometric figure pages in `v8-iso/pages/`. These render on canvas/SVG with
> minimal DOM — mostly a canvas plus a `.cap` caption.

**Why it exists.** The figures are *engineering schematics* of V8 internals rendered as isometric
machines. A chartreuse or cyan accent would read as decoration; the schematic must read as
machined metal and drafting ink. So this family is **monochrome by intent** — the absence of hue
is the design decision, not an omission.

## B1. Color

Fully achromatic. Token set (from `v8-iso/pages/fig-*.html`):

| Role | Token | Dark value |
|---|---|---|
| Background | `--bg` | `#0c0d0e` |
| Panel | `--panel` | `#141516` |
| Edge / outline | `--edge` | `#232629` |
| Line / hairline | `--line` | `#586068` |
| Rib / hatch | `--rib` | `#2e3338` |
| Live / highlight | `--live` | `#f4f6f7` |
| Ink (secondary) | `--ink` | `#8a9096` |
| Ink (high) | `--ink-hi` | `#e8ecee` |
| Body ramps | `--bd0…--bd3` | `#111315` → `#262b30` |
| Dark ramps | `--dk0…--dk2` | `#0b0c0e` → `#16191c` |
| Highlight ramps | `--hi0…--hi3` | `#8e959c` → `#e8ecef` |
| Tag background | `--tag-bg` | `#191c20` |

A light theme exists under `[data-theme="light"]` and is driven by the same `postMessage`
`v8-iso-theme` broadcast the main site sends (`site/src/App.tsx:56-58`, `v8-anatomy.html` script).
Figures also report their rendered height back via `postMessage({ type: 'v8-iso-height', id, height })`.

**Rules.** No hue. Value and edge weight carry all the meaning. If a figure needs to show
"this part is live/active", it shifts *value* (`--live` / `--hi*`), never saturation.

## B2. Typography & type

`--mono` (monospace) is the only family used inside figures — the drawings are annotated like a
technical drawing. Labels are small, tracked-out, and machine-like. Captions (`.cap`) sit outside
the canvas.

## B3. Motion

Figures are **interactive but calm** — the embedded shell responds to pointer interaction and
theme broadcasts; there is no ambient looping animation. Anything animated inside a figure must be
directly tied to user input (e.g. a moving conveyor under the pointer), never decorative.

---

# FAMILY C — Legacy Demo

> Covers `irrigation.html` with `styles.css` (base) + `irrigation.css` (console). Retained for
> the Verus-verified irrigation controller demo. Extend consistently; do not propagate into
> new product surfaces.

## C1. Color

**Dark only — no theme toggle, no `data-theme`.**

| Role | Token | Value |
|---|---|---|
| Background | `--bg` | `#070b16` |
| Panel | `--panel` | `#0d1424` |
| Line | `--line` | `#1d2a44` |
| Text | `--text` | `#e6edf7` |
| Muted | `--muted` | `#8ea0bf` |
| **Accent** | `--accent` | **`#4dd4ff`** (cyan) |
| **Accent 2** | `--accent2` | **`#8f7bff`** (violet) |

Extended (hard-coded, not tokenised) surfaces and strokes:

`#050912` deepest (code/term surfaces) · `#090f1d` alternating section band · `#0a1120` runtime
card · `#0a1222` pump/valve fill · `#1a0d16` setup/warning surface · `#23324f` pipe stroke ·
`#2b3d5e` figure strokes · `#33415c` terminal dots · `#5d7599` code comments / inactive dot.

Status palette (the Family C analog of the tone system — **class modifiers, not `data-tone`**):

| Class | Text | Border / surface |
|---|---|---|
| `.good` | `#6ff0b0` | `#1f5a43` |
| `.bad` | `#ff7a93` | `#6b2236` (surface `#3a1220` for `.load-error`) |
| `.warn` | `#ffcf6b` | — |
| `.muted` | `--muted` | `--line` |

Additional state colors: `#3ee08f` (online, with `box-shadow: 0 0 10px` glow) · `#2f7d4f` (moisture
ok) · `#b5733f` (dry) · `#2d8fd1` / `#1d5f8a` (wet) · `#7a4b2a` (dry legend swatch).

## C2. Typography

**System font stack only** — `-apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial,
sans-serif` at `16px/1.6`. Mono is `ui-monospace, SFMono-Regular, Menlo` for code and values.

Scale: hero h1 `clamp(56px, 10vw, 116px)` / `letter-spacing .14em` / `line-height .95` ·
section h2 `clamp(28px, 4vw, 42px)` · card h3 20px · tagline `clamp(17px, 2.2vw, 24px)` ·
panel head 13px uppercase `letter-spacing .2em` in `--accent2` · eyebrow 11px uppercase
`letter-spacing .28em` in `--accent` · card index / flow label 11px uppercase `letter-spacing .18em`
· body 16px · card p 14px · card list 13px · table 13px · terminal 13px/1.8.

This family is **not** part of the Archivo/Manrope/JetBrains Mono system. Do not add webfonts to
it without treating it as a migration.

## C3. Spacing & layout

- Gutters are viewport-relative: `6vw`. Section padding `88px 6vw` (60px mobile).
- `.grid` — `repeat(auto-fit, minmax(260px, 1fr))`, gap 18px. `.grid.two` — `minmax(320px, 1fr)`.
- `.irr-grid` — `minmax(0,1.7fr) minmax(280px,1fr)`, gap 20px (collapses ≤900px).
- `.panel` — padding 18px 20px. `.card` — padding 26px. `.table-wrap` — overflow-x auto.
- `.meta` — `grid-template-columns: max-content 1fr`, gap 6px 24px.
- Breakpoints: **900px** (`.irr-grid` → 1 column) and **700px** (nav stacks and centers, stats
  2-up, section padding 60px, `.grid.two` → 1 column, `.meta` → 1 column).

## C4. Radii & motion

Radii 4px (cta, flow-step, buttons) · 6px (card, panel, table-wrap, setup) · **999px** (chips,
pills, badges, `.conn` status pill, filter buttons).

**Family C is the one family with continuous animation** — and it must keep a reduced-motion
fallback:

| Animation | Duration | Easing | Trigger |
|---|---|---|---|
| `spin` (pump rotor) | 0.8s | linear, infinite | `.pump-on` |
| `flow` (flowing water) | 0.6s | linear, infinite | `.open` |
| `drip` (droplets) | 1.2s | ease-in, infinite | `.open`, staggered 0.4s |
| hover | — | — | `filter: brightness(1.15)` |

Every one of these is disabled under `@media (prefers-reduced-motion: reduce)`. **Any new
animation in this family must ship with a reduced-motion fallback.**

---

## 4. Component library

Full source for every component is in `.superdesign/init/components.md`; layout/shell source is in
`.superdesign/init/layouts.md`; the extraction menu with source paths, props and hardcoded
elements is in `.superdesign/init/extractable-components.md`.

### Family A — layout components
`TopNav` · `PageShell` · `HeroBand` · `ScoreboardStrip` · `HardwarePillarStrip` ·
`ProvenanceFooter` · `SpecRow` · `SectionLead` · `ArchitectureDiagram` · `ProofDag` ·
`GalleryTopbar` · `JumpNav` · `SegGroup` · `MachineCard` · `CounterpartPill`

### Family A — basic components
`StatTile` · `DigestPill` · `DetailsRow` · `Field` · `ScaleCompare` · `Source` · `FilterBar` ·
`StateSelector` · `TabBar` · `CodeWorkbench` · `InlayBadge` · `DataTable` · `CTAAction` ·
`StatusDot` · `ToneLabel` · `IconSet` · `RatchetBox` · `LoadError`

### Family C — components
`Nav` · `Brand` · `Hero` (image + scrim + content) · `Chips` · `StatsBand` · `Card` · `Term` ·
`Flow` · `DataTable` · `Pill` · `Badge` · `FilterChips` · `MetaList` · `Footer` ·
`ConnStatus` · `Setup` · `Panel` · `Legend` · `VerifyResult` · `RuntimeCard` · `ProbeList` ·
`SimControls` · `MoistureBar` · `EventLog` · `JobLog`

### Family B — components
`FigureCanvas` · `Caption` · `Tag`

### Usage rules (Family A)

1. Every status-bearing element takes a `tone`; never infer status from color alone — pair the
   color with a dot, badge, label, or border.
2. Interactive controls are `<button>` with `data-active` for selected state, `aria-pressed` /
   `aria-expanded` for assistive tech.
3. Data tables get a mono meta bar with the row count on the left and a usage hint on the right.
4. Disclosure uses native `<details>` / `<summary>` — `DetailsRow` — not a JS accordion.
5. Code blocks are always monospace on `--ch-bg-code`, with line numbers and state-coloured rows.
6. Buttons: `.ch-cta-primary` (accent fill + accent ink) for the single primary action per
   view; `.ch-cta-secondary` (outlined) for everything else.
7. `@clickhouse/click-ui` is used sparingly (`Switch`, `Badge`, `Button`). For anything else, use
   the `ch-` classes so the page stays visually consistent.

### Usage rules (Family C)

1. Status uses class modifiers (`.good` / `.bad` / `.warn` / `.muted`), **not** `data-tone`.
2. Cyan `--accent` is the interactive colour; violet `--accent2` labels *structural* groupings
   (panel heads, flow labels, event kinds) — not interactive elements.
3. Any new animation ships with a `prefers-reduced-motion` fallback.
4. The `.conn` connection pill is the canonical live-status indicator: `data-state` of
   `connecting` / `online` / `offline`, with the dot colour and glow doing the work.

---

## 5. Content rules

- **Never hand-type a metric.** Every number comes from `browser/ratchet.json` or
  `data/stats.json` at runtime. Missing data renders the exact string `not recorded`.
- **Name the standard.** Claims cite the upstream spec and its pinned commit (e.g. WHATWG URL
  `4f461b81`, ECMA-262 clauses, WebAssembly 1.0).
- **Show the limit.** Every verified claim is paired with what is *not* yet verified.
- **Source links are monospace and underlined** (`.ch-mono-link`), pointing at the exact file.
- Timestamps and input digests appear in the footer so any figure can be traced to a run.
- Inline code in prose is monospace, 0.87–0.88em, on `--ch-bg-card` with a hairline border and
  3px radius.
- **Isometric metaphor pairs are the house voice.** Each V8 subsystem is named after a piece of
  industrial hardware — "Hidden Classes → Automated Turret Punch Press", "Orinoco Old Space →
  AS/RS High-Bay Warehouse". Keep this register: it explains machine structure through
  machine structure.

---

## 6. Hard requirements for any new surface

1. **Declare the family** (A, B, or C) before designing, and use only that family's fonts,
   colors, spacing, radii, and component styles. Do not mix families on one page.
2. Use the four-state tone system (A) or the class-modifier status palette (C) for every status
   claim. Never infer status from color alone.
3. Every metric is runtime-loaded, with `not recorded` as the failure value.
4. Family A and B must work in both themes — design dark-first, then verify light by overriding
   the same variables; never hard-code a hex value in a component.
5. Hit the family's breakpoints without horizontal scrolling.
6. Keyboard reachable with a visible focus ring (`2px solid var(--ch-accent)` in A).
7. Respect the two-column spec layout when placing prose beside evidence.
8. Reproduce real brand assets — `assets/conduit-mark.png` is the emblem; isometric hardware
   icons are `assets/hw-*.webp`; section medallions are `assets/sticker-*.webp`. Use placeholder
   blocks only for photographic content.
9. Any new animation in Family B or C must be tied to user input (B) or ship a reduced-motion
   fallback (C).

---

## 7. What this system deliberately does not do

- No marketing hero with a gradient headline, no floating 3D blobs, no glassmorphism beyond the
  one frosted hero band in Family A.
- No dark-mode-only surfaces in Family A or B; no pure black (`#000`) backgrounds; no pure white
  text on light.
- No greenfield "feature grid + pricing table + testimonials" landing-page scaffolding.
- No palette drift — chartreuse is Family A's only accent, Family B has none, Family C keeps
  cyan + violet.
- No motion beyond 120–140ms state feedback in Family A.
- No rounded-pill everything in Family A; 4px radii are the norm, pills are reserved for small
  chips.
- No color in the isometric figures — they are schematics, not illustrations.
