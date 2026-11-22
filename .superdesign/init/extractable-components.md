# CONDUIT Extractable Components

Catalog of components that can become reusable Superdesign `DraftComponent` entities (rendered as
`<sd-component>` tags inside design drafts). Prioritised: **layout components first** — they
appear on every surface and benefit most from extraction. Simple primitives (Button, Input, Card)
are deliberately *not* listed; they are cheaper as inline HTML in a draft.

Full source for every component is in `components.md`; layout/shell source is in `layouts.md`.

---

## Layout Components

### TopNav
- Source: `site/src/App.tsx:116-165`
- Category: layout
- Description: Sticky 54px topbar — brand mark + wordmark, section anchor nav, external links, theme switch
- Extractable props: `theme` (string, default: `"dark"`), `activeSection` (string, default: `"coverage"`), `brandText` (string, default: `"CONDUIT"`), `brandMarkSrc` (string, default: `"assets/conduit-mark.png"`), `showThemeToggle` (boolean, default: true)
- Hardcoded: nav labels (Zero-days / Proofs / Why boundaries / Architecture / Live status), link labels (Design doc / V8 anatomy / Irrigation demo / GitHub), `ch-topbar-right` divider, all CSS classes, `IconExternal` glyph
- Notes: the brand mark is `assets/conduit-mark.png` — pass the real asset so the draft reproduces the actual identity, not a generic placeholder

### PageShell
- Source: `site/src/App.tsx:114`
- Category: layout
- Description: Full-height vertical flex column wrapping topbar → content → footer
- Extractable props: `maxWidth` (string, default: `"1380px"`)
- Hardcoded: `ch-page-shell` class, `id="top"`

### HeroBand
- Source: `site/src/App.tsx:194-230` (band) with `site/src/App.tsx:168-256` (section)
- Category: layout
- Description: Full-width frosted-glass band with a kicker row, a 3-up grid of interactive figures, and a link out to the full gallery
- Extractable props: `kicker` (string, default: `"Tier-1 V8 mandatory core"`), `subtitle` (string), `linkLabel` (string, default: `"All 8 core figures"`), `linkHref` (string, default: `"v8-anatomy.html"`), `figureCount` (number, default: 3)
- Hardcoded: `--ch-glass-band` gradient, `backdrop-filter: blur(16px) saturate(1.3)`, chartreuse top/bottom borders, `ch-hero-glass` / `ch-hero-glass-inner` / `ch-hero-glass-bar` CSS, `IconArrowRight` glyph
- Notes: the 3 slots are iframes of `v8-iso/pages/fig-*.html` — in a draft use placeholder blocks, not the live iframes

### ScoreboardStrip
- Source: `site/src/App.tsx:259-341`
- Category: layout
- Description: Full-width live telemetry bar — 4 metric tiles in a grid + a narrow column of 2 provenance pills
- Extractable props: `tiles` (array, default: 4 tiles), `pills` (array, default: 2 pills)
- Hardcoded: `minmax(0,1fr) 356px` grid, `ch-scoreboard-strip` background `--ch-bg-bar`, all tile CSS
- Notes: the app caps this at **exactly 2** provenance pills by design — keep the count fixed

### HardwarePillarStrip
- Source: `site/src/App.tsx:344-375`
- Category: layout
- Description: 4-up row of architecture pillars on a masked drafter-grid background; each is a 78px isometric hardware icon + title + one-line description
- Extractable props: `items` (array of `{ icon, title, sub, href }`, default: 4 items)
- Hardcoded: 28px grid texture, the vertical mask (`transparent 0%, #000 18%, #000 82%, transparent 100%`), `drop-shadow` on icons, hover `background: var(--ch-accent-dim)`
- Notes: icon assets are `assets/hw-*.webp` — pass them as context so the real emblem shows

### ProvenanceFooter
- Source: `site/src/App.tsx:438-486`
- Category: layout
- Description: Mono-type footer — brand mark, live data-source links, ratchet timestamp + inputs digest
- Extractable props: `generatedAt` (string, default: `"not recorded"`), `inputsDigest` (string, default: `"not recorded"`)
- Hardcoded: footer links (browser/ratchet.json, data/stats.json, V8 anatomy, Irrigation demo, Design doc, GitHub), `--ch-bg-bar` background, `ch-mono-link` styling

### SpecRow
- Source: `site/src/site.css:786-820` + the section pattern in `site/src/SectionCoverage.tsx:46-209`
- Category: layout
- Description: The Tufte two-column executable-specification row — 440px prose column beside a flexible artifact column, hairline top border, `scroll-margin-top: 70px`
- Extractable props: `id` (string, default: `"section"`), `prose` (slot), `artifact` (slot), `flush` (boolean, default: false), `sub` (boolean, default: false)
- Hardcoded: `grid-template-columns: 440px minmax(0, 1fr)`, `gap: 36px`, `padding-top: 44px`, 1px `--ch-border-subtle` top rule

### SectionLead
- Source: `site/src/SectionCoverage.tsx:48-59` (pattern), CSS `site/src/site.css:821-874`
- Category: layout
- Description: Section header — 72–76px isometric sticker medallion beside a 25px Archivo title
- Extractable props: `iconSrc` (string, default: `"assets/sticker-shield.webp"`), `iconAlt` (string), `title` (string, default: `"Section title"`), `align` (string, default: `"center"`)
- Hardcoded: `drop-shadow(0 6px 12px rgba(0,0,0,.34))`, `--ch-sticker-medallion`, title typography

### ArchitectureDiagram
- Source: `site/src/parts.tsx:91-169`
- Category: layout
- Description: Tiered trust-boundary diagram — ingress row → verified kernel shell → dashed IPC capability rail → 3 sandboxed renderers + isolation-theorem caption
- Extractable props: `renderers` (array, default: 3 renderers), `kernelNodes` (array, default: 3), `ingressNodes` (array, default: 2)
- Hardcoded: the three tier headings, the IPC rail copy ("Typed Vest-encoded IPC — capability handles only, zero ambient authority"), the isolation-theorem caption, `data-trust="verified"|"untrusted"` semantics, `IconArrowRight` / `IconArrowDown` glyphs

### ProofDag
- Source: `site/src/parts.tsx:171-310`
- Category: layout
- Description: Interactive SVG dependency graph of proof obligations — two columns (specs/primitives → implementations/theorems), bezier edges, click-to-trace with dimming and an inspector strip
- Extractable props: `nodes` (array, default: 8 nodes), `edges` (array, default: 8 edges), `verified` (boolean, default: true)
- Hardcoded: `nodeW 248`, `nodeH 44`, `colX [24, 412]`, `rowPitch 58`, column headings, the inspector sentence templates

---

## Basic Components

### StatTile
- Source: `site/src/parts.tsx:7-26`
- Category: basic
- Description: Metric tile — large tabular-numeral value, uppercase mono label, muted hint, optional status icon
- Extractable props: `value` (string, default: `"0"`), `label` (string, default: `"metric"`), `hint` (string, default: `""`), `tone` (string, default: `"neutral"`)
- Hardcoded: 24px mono value, 10.5px uppercase mono label, the proved/warn/fail icon mapping

### DigestPill
- Source: `site/src/App.tsx:306-338`
- Category: basic
- Description: Copyable provenance chip — status dot + mono value on the left, meta + copy glyph on the right
- Extractable props: `value` (string, default: `"not recorded"`), `meta` (string, default: `""`), `tone` (string, default: `"neutral"`), `copiedLabel` (string, default: `"copied"`)
- Hardcoded: 36px min-height, `ch-digest-meta` left border, `IconCopy` glyph

### DetailsRow
- Source: `site/src/parts.tsx:35-55`
- Category: basic
- Description: Disclosure row — status dot, mono key, value, mono meta, rotating chevron, expandable body of `Field` rows
- Extractable props: `k` (string, default: `"01"`), `v` (string, default: `"Row title"`), `meta` (string, default: `""`), `tone` (string, default: `"neutral"`), `open` (boolean, default: false)
- Hardcoded: 90deg chevron rotation on open, `--ch-det-k` accent colour, `ch-det-dot` tone colours

### Field
- Source: `site/src/parts.tsx:28-33`
- Category: basic
- Description: Definition-list row — uppercase mono term above a sans-serif definition, hairline separator between siblings
- Extractable props: `label` (string, default: `"Label"`)
- Hardcoded: 10.5px uppercase mono `dt`, 13.5px `dd`, sibling separator rule

### ScaleCompare
- Source: `site/src/parts.tsx:57-89`
- Category: basic
- Description: Log-scale horizontal bar comparison with label, tabular value, bar track and an italic axis note
- Extractable props: `items` (array of `{ id, label, lines, display, tone, note }`, default: 4 items), `axisNote` (string, default: `"Logarithmic scale — each major step represents 10× more source code."`)
- Hardcoded: 12px track height, log-scaled bar widths, `min-width: 4px` bar floor

### Source
- Source: `site/src/parts.tsx:312-316`
- Category: basic
- Description: Underlined monospace source link, accent-coloured
- Extractable props: `href` (string, default: `"#"`), `text` (string, default: `"source"`)

### FilterBar
- Source: `site/src/SectionCoverage.tsx:133-155`
- Category: basic
- Description: Wrapping row of toggle buttons, each with a label and a mono count; active state is accent-tinted
- Extractable props: `filters` (array of `{ id, label, count }`, default: 4 filters), `activeId` (string, default: `"all"`)
- Hardcoded: `gap: 8px`, `padding: 7px 12px`, 12.5px semibold sans labels, 11px mono counts

### StateSelector
- Source: `site/src/site.css:1104-1169` (pattern used by `SectionVerus.tsx`)
- Category: basic
- Description: 2-column grid of the four Verus obligation states (verified / failed / timeout / admit), each a bordered card with mono title + muted summary
- Extractable props: `states` (array of `{ id, title, summary, tone }`, default: 4 states), `activeId` (string, default: `"verified"`)
- Hardcoded: 1fr 1fr grid, `padding: 10px 12px`, tone-tinted active borders/backgrounds

### TabBar
- Source: `site/src/site.css:1175-1201`
- Category: basic
- Description: Mono-type tab switcher; active tab is accent-tinted with an accent border
- Extractable props: `tabs` (array of `{ id, label }`, default: 3 tabs), `activeId` (string, default: `""`)
- Hardcoded: `gap: 8px`, `padding: 8px 14px`, 12px mono semibold labels

### CodeWorkbench
- Source: `site/src/site.css:1228-1414` (pattern used by `SectionVerus.tsx`)
- Category: basic
- Description: Dark code panel — header strip, scrollable code rows (lineno / glyph / lane pill / text), and expandable Z3 counterexample inlays with state badges
- Extractable props: `title` (string, default: `"crate.rs"`), `rows` (array of `{ n, text, lane, state, glyph }`, default: 8 rows), `tone` (string, default: `"proved"`)
- Hardcoded: `--ch-bg-code` background, 23px line-height, `max-height: 540px` scroll area, lane-pill colours, `ch-z3-inlay` grid-span behaviour

### InlayBadge
- Source: `site/src/site.css:1381-1408`
- Category: basic
- Description: Small uppercase monospace state badge — bordered, tinted background matching its tone
- Extractable props: `label` (string, default: `"VERIFIED"`), `tone` (string, default: `"proved"`)
- Hardcoded: 10.5px uppercase mono, `letter-spacing: .05em`, `padding: 2px 7px`, radius 3px

### DataTable
- Source: `site/src/site.css:2020-2107` (pattern used in `SectionCoverage.tsx:157-207`, `SectionWhy.tsx:86-113`)
- Category: basic
- Description: Card-wrapped table with a mono meta bar (left: count, right: hint), uppercase mono column heads, zebra-free hover highlight, and an optional interactive/selected row state
- Extractable props: `meta` (string, default: `""`), `metaHint` (string, default: `""`), `columns` (array of strings, default: 4), `rows` (array, default: 5), `interactive` (boolean, default: false)
- Hardcoded: `--ch-bg-bar` meta bar and header row, 1px row separators, `.ch-num` right-align + tabular numerals, `.ch-total-row` emphasis

### CTAAction
- Source: `site/src/site.css:509-542` (pattern used in `site/src/App.tsx:243-252`)
- Category: basic
- Description: Primary (accent-filled) or secondary (outlined) call-to-action link
- Extractable props: `label` (string, default: `"Explore"`), `href` (string, default: `"#"`), `variant` (string, default: `"primary"`), `withArrow` (boolean, default: true)
- Hardcoded: `padding: 10px 18px`, 13.5px semibold, radius 4px, 140ms transitions, `IconArrowRight` glyph

### StatusDot
- Source: `site/src/site.css:931-952`
- Category: basic
- Description: 7px inline status circle
- Extractable props: `tone` (string, default: `"neutral"`)
- Hardcoded: 7px circle, `margin-right: 8px`, tone colours

### ToneLabel
- Source: `site/src/site.css:954-967`
- Category: basic
- Description: Inline text label coloured by tone — the text form of a status
- Extractable props: `tone` (string, default: `"neutral"`), `text` (string, default: `""`)

### IconSet
- Source: `site/src/icons.tsx`
- Category: basic
- Description: 8 stroked 16×16 icons — Check, X, Clock, ShieldAlert, Copy, External, Chevron, ArrowDown, ArrowRight
- Extractable props: `name` (string, default: `"check"`), `size` (number, default: 14)
- Hardcoded: `stroke-width: 1.6`, round caps/joins, `currentColor`
- Notes: icons inherit `currentColor` — they must be reproduced 1:1, not substituted with generic glyphs
