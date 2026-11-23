# The Drafting Room — exploded isometric icons, illustrations, and tiered visualization components

Status: approved 2026-11-22. Owner: Chief (team lead). Scope: Phase 1 only.

## 1. Context

CONDUIT Lab is a browser engine whose security-critical code is proved against its published
standard by Verus/Z3. Two machinery engines already exist in this repository:

| Engine | Location | Capability |
|---|---|---|
| Isometric CAD | `v8-iso/iso-cad.mjs` | Dependency-free isometric renderer emitting live SVG. Primitives: `box3`, `cyl`, `revolve`, `loft`, `extrudePoly`, `sweepTube`, `stadium2D`, `gear2D`, `helix3D`. Has `callout()` for leader+label. 11 published plates (8 figures + 3 showcases). |
| Mechanical drawing | `inkwork/` | Three.js engine: exploded assemblies, section views, first-angle three-view, BOM balloons, pencil hatching, paper/blueprint palettes. 5 machines (turboprop, maglev, macbook, model3, coupling). MIT, orionsheep. |

The target aesthetic — the "quintessential motorcycle magazine" exploded cutaway plate — is a
specific anatomy, and `v8-iso` currently implements only two of its nine features:

1. exploded separation along a dominant axis — **missing**
2. hairline leader lines with terminal dot — **present** (`callout()`)
3. circled part numbers (balloons) — **missing**
4. 45° section hatching on cut faces, opposed direction on adjacent parts — **missing**
5. dash-dot centerlines through symmetric features — **missing**
6. dimension lines with extension + terminators — **missing**
7. parts list / BOM — **missing**
8. consistent isometric projection — **present**
9. hairline stroke discipline, no fill-as-shadow — **present**

`docs/site-redesign-proposal.md` already fixes the palette and craft rules ("craftsman drafter,
restrained futuristic"): hairline rules, exact registration, dimension lines, deep ink/graphite
ground, one desaturated phosphor accent reserved for live-verified status, amber/red for warn/fail.

**Therefore this is not a drawing from scratch.** It is an extension of a real engine, plus a
first-class React component layer over both engines, plus a tiered visualization component library.

## 2. Goals

- **G1** — Icons and illustrations in exploded isometric form, depicting machinery that actually
  exists in this repository, rendered in the motorcycle-magazine cutaway grammar on this repo's
  drafter board.
- **G2** — A React 19 component library for visualization at the highest level of React quality,
  covering three genres (animated numbers/stats, interactive 3D, algorithm scenes) in one motion
  system and one visual grammar.
- **G3** — Zero coupling to the live site. Nothing is added to or modified in `site/`.

## 3. Non-goals (explicit)

- **N1** — Do not modify, import into, or wire anything into `site/`, `site/src/App.tsx`, or the
  `npm run build` → `dist/` pipeline. The components are built, reviewed and mergeable, but
  **not connected**. This is an explicit instruction from the requester.
- **N2** — No mock data. Every metric renders from `browser/ratchet.json` / `data/stats.json`, or
  is computed in-browser. Missing data renders `not recorded` (Constitutional Law 2,
  `docs/site-redesign-proposal.md`).
- **N3** — No paper/light-board variant in Phase 1. One theme: the dark drafter board.
- **N4** — No edits to `v8-iso/` or `inkwork/` source. The engine is *read* and *adapted into*
  `atelier/`; the originals stay authoritative for the site.

## 4. Architecture

A new, isolated workspace at repository root: `atelier/`.

```
atelier/
  package.json          # name: conduit-atelier, private
  vite.config.ts
  tsconfig.json
  index.html
  src/
    main.tsx
    App.tsx             # gallery shell + route switch
    contract/           # OWNED BY CHIEF — frozen before dispatch
      index.ts          # public types every team member codes against
      tokens.ts         # palette + stroke + motion tokens
    illustration/       # OWNED BY Drafter
      engine/           # ported + extended CAD engine
      icons/            # 8 icon components
      plates/           # 2 large illustrations
    viz/
      stats/            # OWNED BY Motion   (Tier 1)
      stage/            # OWNED BY Stage    (Tier 2 + Tier 3)
    gallery/            # OWNED BY Proof
  tests/                # OWNED BY Proof
```

**Why a separate app.** `site/` builds to `dist/` on every push and is verified by Playwright
against `ratchet.json` and `stats.json`. Adding unverified component work to that pipeline risks
the published site and the CI contract. An isolated workspace keeps `npm run build` untouched
while the components mature.

### 4.1 Frozen contract

`atelier/src/contract/` is written by Chief **before** any other bot starts, and defines:

```ts
/** How a part's geometry is defined, in world units. Mirrors the primitives
 *  already present in v8-iso/iso-cad.mjs, which the engine port reuses. */
export type GeometrySpec =
  | { kind: 'box'; at: Vec3; size: Vec3 }
  | { kind: 'cyl'; from: Vec3; to: Vec3; r0: number; r1?: number }
  | { kind: 'revolve'; profile: Vec2[]; segments: number }
  | { kind: 'loft'; stations: Vec3[] }
  | { kind: 'extrude'; poly: Vec2[]; depth: number }
  | { kind: 'tube'; points: Vec3[]; radius: number };

export type Vec2 = [number, number];
export type Vec3 = [number, number, number];

// A drawing primitive in world space, rendered by the illustration engine.
export interface Part {
  id: string;
  label: string;
  /** Optional balloon number. If absent the part is unlabelled. */
  balloon?: number;
  /** Explode offset along the assembly axis, in world units. */
  explode?: [number, number, number];
  /** Parts whose faces are cut and hatched. */
  sectioned?: boolean;
  geometry: GeometrySpec;
}

// Public props for every icon component.
export interface IconProps {
  size?: number;              // default 32
  className?: string;
  /** 'proved' | 'warn' | 'fail' | 'neutral' — drives accent semantics only. */
  tone?: Tone;
  /** Show balloons and leader lines. Default true for plates, false for inline icons. */
  annotated?: boolean;
  title?: string;             // accessible name; omit for decorative
}
```

Icons are **React components emitting inline SVG**, never `<img>` and never raster. Every
instance namespaces its SVG `id`s via React 19 `useId` so dozens can coexist on one page without
`url(#...)` collisions.

## 5. The Drawing Standard

This is the normative visual grammar. Chief signs it off; every member codes against it.

### 5.1 Palette (tokens)

| Token | Value | Use |
|---|---|---|
| `--board-0` | `#0c0d0e` | Page ground |
| `--board-1` | `#141516` | Plate / panel |
| `--board-2` | `#1a1d20` | Raised plate |
| `--line` | `#586068` | Structural hairline |
| `--rib` | `#2e3338` | Ribs, hidden edges |
| `--edge-hi` | `#b2b8be` | Cut edges |
| `--ink` | `#8a9096` | Labels, notes |
| `--ink-hi` | `#e8ecee` | Emphasis, title block |
| `--live` | `#f4f6f7` | Proved / knockout |
| `--accent` | `#74c7b0` | Phosphor teal — live-verified status ONLY |
| `--warn` | `#d9a441` | Warning |
| `--fail` | `#d4645c` | Failure |
| `--shade-0..5` | ramp | Face shading by normal |

Accent is reserved. If everything glows, nothing is verified. Amber and red appear only on
failure paths.

### 5.2 Stroke discipline

| Class | Width | Line style |
|---|---|---|
| Structure | `1.05` | solid |
| Cut edge | `1.35` | solid |
| Hidden edge | `0.75` | dashed `2.5 2` |
| Centerline | `0.6` | dash-dot `8 2 1.6 2` |
| Section hatch | `0.5` | solid, 45° or 135°, ~0.5 opacity |

All strokes use `vector-effect: non-scaling-stroke`, `stroke-linecap: round`,
`stroke-linejoin: round`. **No drop shadows.** No gradient fills used as pseudo-shadow. Depth is
communicated by face shading ramp and stroke weight only — 1–2px umbra on interactive controls
is the single exception, per the redesign proposal.

### 5.3 Motorcycle-magazine anatomy

1. **Exploded axis** — parts separate along one dominant axis with a consistent gap. The gap is
   uniform per assembly; parts that stay bolted together (a sub-assembly) explode as a unit.
2. **Leader line** — `0.9` dashed hairline from the part's own surface to a terminal dot (`2`
   radius, filled `--live`), then to a label pill. Leader never crosses another leader.
3. **Balloon** — circle `r=9`, `1` stroke, numeral centered in 9px mono. Balloons are numbered
   in assembly order and map to the parts list.
4. **Section hatching** — 45° parallel hatch on cut faces. **Adjacent parts hatch in opposite
   directions** (45° / 135°) so cuts read apart. This is the single most recognisable magazine
   cue and it is mandatory on any cut.
5. **Centerlines** — dash-dot through every axis of symmetry, extending ~3% past the feature.
6. **Dimension lines** — extension lines from the feature, a dimension line between them with
   tick terminators, and a mono value label.
7. **Parts list** — a hairline-ruled table: balloon number, part name, count. No quantities or
   dimensions (that is `inkwork`'s territory).
8. **Title block** — hairline rule, figure number, plate name, scale, part count.
9. **Projection** — isometric at azimuth 42°, elevation 30° (matching `v8-iso/iso-cad.mjs`
   defaults) so plates in the gallery read as one set.

### 5.4 Register

Labels are uppercase mono at 9–10px with `0.04–0.09em` tracking, matching `v8-iso`. Body prose is
JetBrains Mono. No decorative typeface anywhere in the atelier.

## 6. Deliverables

### 6.1 Icons — 8 components (`illustration/icons/`)

Each is an exploded isometric assembly with balloons, leader lines and section hatching on cut
faces. Subject is machinery that exists in this repository:

| Slug | Subject | Source of truth |
|---|---|---|
| `isolate` | `v8::Isolate` — twin-silo process skid | `v8-iso/pages/fig-01-isolate.html` |
| `pointer-tagging` | Tagged pointer lattice | `fig-02-pointer-tagging.html` |
| `hidden-classes` | Hidden-class transition tree | `fig-03-hidden-classes.html` |
| `parser` | Lexer → Pratt parser pipeline | `fig-04-parser.html` |
| `ignition` | Bytecode dispatch loop | `fig-05-ignition.html` |
| `old-space` | GC old generation | `fig-07-old-space.html` |
| `new-space` | Scavenger nursery | `fig-08-new-space.html` |
| `ratchet` | The trusted-item ratchet | `browser/ratchet.json` semantics |

Each icon: `size` prop works from 24 to 256px, `tone` prop, `annotated` prop toggles balloons,
inline SVG, `useId` namespacing, accessible name via `title` prop.

### 6.2 Illustrations — 2 plates (`illustration/plates/`)

1. **V8 Mandatory Core, exploded** — the eight core machines as one continuous exploded assembly
   along a shared axis. The hero plate.
2. **Verified kernel vs. sandboxed renderer** — the strategy plate from Act 3 of the redesign
   proposal: proved kernel in front of disposable per-site renderers, with design-only
   components (kernel, Nanvix, HTML/CSS) **hatched** to read as "not yet proved".

### 6.3 Tier 1 — animated numbers & stats (`viz/stats/`)

Remotion/Remocn DNA, in the drafter grammar. Remocn's `numbers` catalog is the benchmark for
choreography quality; this implementation differs by using the repo's palette, the repo's real
data, and the drafting craft rules.

Components: `CountFigure`, `OdometerReels`, `StatTile` (animated reveal), `SplitBar`,
`RadialGauge`, `DeltaChip`, and the hero `RatchetCounter`.

`RatchetCounter` is the signature piece: it displays the trusted-item count and animates
**downward** only. When the count would rise, it does not animate up — it flashes `--fail` and
holds, because the ratchet's whole meaning is that the number never rises between releases.

### 6.4 Tier 2 — interactive 3D (`viz/stage/`)

Math3d DNA: a WebGL scene, orbit/pan/zoom, real geometry.

Scene: **the tri-color GC heap** — white/grey/black objects in a 3D heap space, with the
tri-color invariant visible: a grey object must have no black pointers. Rotating reveals the
barrier violation when one exists.

**Implementation constraint:** use raw `three` in a React wrapper — **not**
`@react-three/fiber`. R3F v8 pins React 18; the atelier app is React 19, and R3F v9 is a
different API surface than `inkwork/` uses. `inkwork/` stays untouched and is read for
reference only. `three` is the only new runtime dependency Phase 1 permits.

### 6.5 Tier 3 — algorithm scenes (`viz/stage/`)

Manim-DSA DNA: step-through animation of a real algorithm from this repo.

1. **Pratt parser** — trace `vjs_syntax` (J3): token stream → precedence climbing → AST.
2. **Tri-color mark-sweep** — trace `vjs_gc` (J6): roots → marking → sweeping → sweeping.

Each scene is a stepper: `play`, `pause`, `step`, `reset`, and a scrubbable timeline. Annotations
name the actual spec clause or invariant being demonstrated.

## 7. Motion grammar

One system for all three tiers. Mechanical, damped, precise — **no bounce, no overshoot, no
spring**.

| Token | Value | Use |
|---|---|---|
| `d1` | 120ms | Micro (balloon fade, label swap) |
| `d2` | 240ms | Standard (stat reveal, digit roll) |
| `d3` | 480ms | Feature (figure count-up, section cut) |
| `d4` | 960ms | Scene (explode assemble, camera settle) |

Easing: `d1/d2` use `cubic-bezier(0.22, 0.61, 0.36, 1)`; `d3/d4` use
`cubic-bezier(0.16, 0.84, 0.44, 1)`. Both are decelerating and settle without overshoot.

Choreography vocabulary, used consistently:

- **draw** — linework draws on via `stroke-dashoffset`
- **assemble** — exploded parts travel to their offset position, staggered along the axis
- **cut** — section face reveals, hatch fades in behind the cut edge
- **settle** — camera/easing settle, no bounce

`prefers-reduced-motion: reduce` renders the final state instantly, with no intermediate
animation. This is a hard requirement, tested.

## 8. Quality bar

- React 19, TypeScript `strict`, no `any`, no `unknown` escapes in public API.
- Public props typed and exported from `contract/index.ts`.
- Colocated `*.test.tsx` (vitest) for units; `atelier/tests/` (Playwright) for interaction.
- Every icon and component has an accessible name; decorative SVG is `aria-hidden`.
- SVG `<title>` present when `title` prop supplied.
- Icons ≤ ~8KB gzipped each.
- 60fps for interactive scenes on the reference machine.
- `prefers-reduced-motion` honored and tested.
- No `document`/`window` access outside effects; no global CSS side effects.
- No new runtime dependencies beyond React, `react-dom`, `three` (Tier 2 only), and a test runner.

## 9. Team structure and file ownership

Chief is the existing main bot (`bot_78e73c73be11`) and is the team lead. Chief creates four
member bots, all with `default_workspace_dir = /Users/mac/conduit-lab`, `auto_helper: true`.

| Bot | Role | Owns (disjoint) | Deliverable |
|---|---|---|---|
| **Drafter** | Illustration engineer | `atelier/src/illustration/**` | Engine extension (hatching, balloons, explode, centerlines, dimensions, parts list) + 8 icons + 2 plates + the Drawing Standard implementation notes |
| **Motion** | Animation engineer | `atelier/src/viz/stats/**` | Tier 1: 6 components + `RatchetCounter` |
| **Stage** | Scene engineer | `atelier/src/viz/stage/**` | Tier 2 GC heap scene + Tier 3 Pratt parser and tri-color GC scenes |
| **Proof** | QA / harness | `atelier/src/gallery/**`, `atelier/tests/**` | Gallery shell, a11y, reduced-motion, vitest + Playwright suites |

**Chief owns** `atelier/src/contract/**`, `atelier/package.json`,
`atelier/vite.config.ts`, `atelier/tsconfig.json`, `atelier/index.html`, `atelier/src/main.tsx`,
`atelier/src/App.tsx` — the shared surface, written and frozen **before** dispatch.

**Disjointness is a hard constraint.** No two bots write the same file. Chief writes the shared
surface first; members build against the frozen contract; Chief integrates.

## 10. Definition of done — Phase 1

1. `atelier/` installs, builds, typechecks with `strict` on, and all tests pass.
2. 8 icon components + 2 plates render, with balloons, leader lines and section hatching.
3. Tier 1: 6 components + `RatchetCounter`, all fed by real `ratchet.json` / `stats.json` data.
4. Tier 2: one interactive WebGL GC heap scene.
5. Tier 3: two step-through algorithm scenes.
6. Gallery renders every piece, dark drafter board, responsive.
7. `prefers-reduced-motion` path verified by Playwright.
8. Accessible names verified; zero console errors; zero React key or hydration warnings.
9. `site/` is byte-identical to its pre-Phase-1 state (`git diff` over `site/` is empty).
10. `docs/drawing-standard.md` written and signed off by Chief.

## 11. Risks

| Risk | Mitigation |
|---|---|
| Bots write conflicting files | Strict disjoint ownership; shared surface frozen up front; only Chief edits the shared surface |
| Bots lack filesystem write access | Fall back: Chief creates them, or MCode creates them directly with identical structure |
| Scope creep past Phase 1 | Explicit non-goals; only Chief may add members or change ownership |
| Components drift from site conventions | Frozen contract + tokens; every member codes against the same published types |
| Mock data creeps in | Constitutional Law 2 is a hard constraint; Proof's tests assert real data wiring |

## 12. References

- `docs/site-redesign-proposal.md` — design language, Constitutional Law 2
- `v8-iso/iso-cad.mjs` — the isometric engine being extended
- `inkwork/` — mechanical drawing reference implementation
- `browser/ratchet.json`, `data/stats.json` — the only permitted data sources
- https://remocn.dev/docs/numbers — Tier 1 choreography benchmark
- https://www.math3d.org/ — Tier 2 benchmark
- https://github.com/F4bbi/manim-dsa — Tier 3 benchmark
