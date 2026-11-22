# CONDUIT Page Dependency Trees

Import traces from each surface, resolved recursively through local files only (`node_modules`
excluded). Each tree is the **candidate set** for `--context-file` when designing that surface —
apply the PAYLOAD BUDGET rule (~900-line threshold) before sending.

---

## `/` — Executable Specification (the main site)

Entry: `site/src/main.tsx` → `site/src/App.tsx`

Renders, in order: sticky topbar → hero (h1 + prose + frosted-glass band of 3 interactive V8
figures + prose + 3 CTAs) → live ratchet scoreboard (4 stat tiles + 2 provenance pills) →
hardware pillar strip (4 items on a drafter-grid) → main spec container (5 sections) → provenance
footer.

Dependencies:

```
- site/src/App.tsx
  - site/src/data.ts                      (types, loaders, ratchet helpers)
  - site/src/icons.tsx                    (IconArrowRight, IconCopy, IconExternal)
  - site/src/parts.tsx                    (ArchitectureDiagram, StatTile)
    - site/src/icons.tsx                  (IconArrowDown, IconArrowRight, IconCheck, IconChevron, IconShieldAlert, IconX)
    - site/src/content/vurl.ts             (types only: ProofDagNode, ProofDagEdge)
  - site/src/content/cves.ts              (CVES, coverage tone maps)
  - site/src/SectionCoverage.tsx
    - @clickhouse/click-ui                (Badge)
    - site/src/data.ts                    (blobUrl)
    - site/src/content/cves.ts            (CVES, COVERAGE_*, coverageTone, Coverage)
    - site/src/parts.tsx                  (Field, Source)
      - site/src/icons.tsx
      - site/src/content/vurl.ts
  - site/src/SectionVerus.tsx
    - @clickhouse/click-ui                (Badge, Button)
    - site/src/data.ts                    (loadText, NR, ProofShowcaseItem, Ratchet)
    - site/src/content/vurl.ts            (VURL_VERIFIED_LINES, COUNTEREXAMPLE_LINES, TIMEOUT_LINES, ADMIT_LINES, VerusCodeLine, VerusLane, ObligationState)
    - site/src/icons.tsx                  (IconCheck, IconClock, IconExternal, IconShieldAlert, IconX)
    - site/src/parts.tsx                  (Source)
      - site/src/icons.tsx
      - site/src/content/vurl.ts
  - site/src/SectionWhy.tsx
    - site/src/data.ts                    (NR, ratchetTotals, Ratchet)
    - site/src/content/systems.ts         (SCALE_ITEMS, SYSTEMS)
    - site/src/parts.tsx                  (DetailsRow, Field, ScaleCompare, Source)
      - site/src/icons.tsx
      - site/src/content/vurl.ts
  - site/src/SectionStatus.tsx
    - @clickhouse/click-ui                (Badge)
    - site/src/data.ts                    (NR, Ratchet, loadJson, ratchetTotals, sumTrusted, ...)
    - site/src/content/tradeoffs.ts       (TRADEOFFS)
    - site/src/content/vjs.ts             (FUEL_THEOREM, VJS_STEPS)
    - site/src/content/vurl.ts            (VURL_DAG_EDGES, VURL_DAG_NODES, VURL_MODULES)
    - site/src/icons.tsx                  (IconExternal)
    - site/src/parts.tsx                  (DetailsRow, Field, ProofDag, Source)
      - site/src/icons.tsx
      - site/src/content/vurl.ts
  - site/src/site.css                     (2420 lines — see theme.md §2c for ranges)
- site/index.html                         (font faces, meta, #root)
```

**Suggested context set for a `/` design call** (sum ≈ 1 500 lines → trim per the rule):

```
--context-file .superdesign/design-system.md
--context-file site/src/site.css:1:135      (tokens + base)
--context-file site/src/site.css:136:235    (shell + topbar)
--context-file site/src/site.css:236:545    (hero)
--context-file site/src/site.css:627:771    (scoreboard + digest pills)
--context-file site/src/site.css:772:968    (Tufte spec layout + prose)
--context-file site/src/site.css:2287:2420  (responsive)
--context-file site/src/parts.tsx
--context-file site/src/icons.tsx
```

---

## Section-level sub-trees

The five spec sections are siblings inside `.ch-spec-container`. Each is a `.ch-spec-row`
(440px prose column + flexible artifact column).

### `#coverage` — CVE coverage map
Entry: `site/src/SectionCoverage.tsx`

```
- site/src/SectionCoverage.tsx
  - @clickhouse/click-ui                  (Badge)
  - site/src/data.ts                      (blobUrl)
  - site/src/content/cves.ts
  - site/src/parts.tsx                    (Field, Source)
```

Prose column: section lead (shield medallion + h2) → prose → 3-item tone tally (proved / warn /
fail) → CVE detail card (CVE id + Badge + 4 `Field` rows) → source note.
Artifact column: filter bar (4 buttons with counts) → `.ch-table-card` with a 5-column interactive
CVE table (status dot + mono CVE id, patched date, component, flaw, response).

### `#proofs` — Verus 4-state workbench
Entry: `site/src/SectionVerus.tsx`

```
- site/src/SectionVerus.tsx
  - @clickhouse/click-ui                  (Badge, Button)
  - site/src/data.ts
  - site/src/content/vurl.ts
  - site/src/icons.tsx
  - site/src/parts.tsx                    (Source)
```

Prose column: section lead → prose → `.ch-state-selector` (2×2 grid of the four obligation states:
verified / failed / timeout / admit) → state summary + fix action.
Artifact column: `.ch-workbench-tabs` → `.ch-code-workbench` (header + scrollable code rows with
lane pills and expandable Z3 counterexample inlays) → live proof picker + proof meta/links.

### `#scope` — Why boundaries, not everything
Entry: `site/src/SectionWhy.tsx`

```
- site/src/SectionWhy.tsx
  - site/src/data.ts
  - site/src/content/systems.ts
  - site/src/parts.tsx                    (DetailsRow, Field, ScaleCompare, Source)
```

Prose column: section lead (knot medallion) → prose → `ScaleCompare` (log-scale bars, CONDUIT
appended with live LOC) → accordion of 4 constraints → source note.
Artifact column: `.ch-table-card` with the "9 landmark systems" table (System / What it proved /
Scale & effort / Lesson for CONDUIT).

### `#arch` — Verified kernel architecture
Entry: inline in `site/src/App.tsx:390-432`

```
- site/src/App.tsx
  - site/src/parts.tsx                    (ArchitectureDiagram)
  - site/src/icons.tsx                    (IconArrowDown, IconArrowRight)
  - site/src/site.css                     (arch blocks, 1683-1873)
```

Prose: section lead (lock sticker medallion) + h2 + prose with inline `<code>` chips.
Artifact: 5fr/7fr split — `.ch-iso-frame` (isometric architecture image + figcaption) beside
`ArchitectureDiagram` (tiered ingress → verified kernel → IPC rail → sandboxed renderers).

### `#ratchet` — Live status
Entry: `site/src/SectionStatus.tsx`

```
- site/src/SectionStatus.tsx
  - @clickhouse/click-ui                  (Badge)
  - site/src/data.ts
  - site/src/content/tradeoffs.ts
  - site/src/content/vjs.ts
  - site/src/content/vurl.ts
  - site/src/icons.tsx
  - site/src/parts.tsx                    (DetailsRow, Field, ProofDag, Source)
```

Wraps a `.ch-status-section` with a flush `.ch-spec-row` (honesty card + disclosure card) then a
sub `.ch-spec-row` containing the vurl module accordion, the `ProofDag`, the J0–J7 track, VM
benchmarks, conformance suites, the fuel theorem contract box, and the tradeoffs accordion.

---

## `/v8-anatomy.html` — V8 isometric gallery

Entry: `v8-anatomy.html` (repo root, 30 252 bytes, fully self-contained)

```
- v8-anatomy.html
  - assets/fonts/*.woff2                  (Archivo / Manrope / JetBrains Mono, inline @font-face)
  - assets/conduit-favicon.png
  - v8-iso/pages/fig-*.html               (11 interactive isometric figures, iframed)
```

Inline `<style>` + inline `<script>`. Uses `data-theme="dark"` on `<html>` and the same
self-hosted fonts as the main site, but **not** the `--ch-*` token layer.

**Context**: pass `v8-anatomy.html` — it is under 900 lines? No: it is ~700 lines of dense HTML.
Use `v8-anatomy.html:1:400` for structure and skip the inline JS.

---

## `/irrigation.html` — Garden irrigation console

Entry: `irrigation.html` (repo root)

```
- irrigation.html
  - styles.css                            (legacy base: nav, hero, panels, buttons, chips)
  - irrigation.css                        (console-specific: .irr grid, .conn pill, .panel, controls)
  - irrigation.js                         (bridge client, valve state, tank level)
```

Visual system **B** (cyan `#4dd4ff` + violet `#8f7bff`, dark only) — see `routes.md`.

**Context**: `irrigation.html` (16 lines of markup) + `irrigation.css` (4 486 bytes) +
`styles.css` (7 505 bytes) — all comfortably under the 900-line threshold, so pass them whole.

---

## `/v8-iso/pages/fig-*.html` — Isometric V8 figures

Entry: `v8-iso/pages/fig-01-isolate.html` … `fig-08-new-space.html`
(+ `showcase-01-jet-engine.html`, `showcase-02-sports-car.html`, `showcase-03-cruise-ship.html`)

Self-contained isometric/SVG figures with their own inline scripts. Embedded into the main site
as `<iframe class="ch-hero-iso-frame" src="v8-iso/pages/fig-03-hidden-classes.html?embed=1&compact=1&theme=dark&id=hero-fig-03-hidden-classes">`.

They receive theme changes via `postMessage({ type: 'v8-iso-theme', theme })` from `App.tsx:56-58`
and report their rendered height back via `postMessage({ type: 'v8-iso-height', id, height })`
(handled at `App.tsx:61-72`).
