# CONDUIT Pages Redesign Proposal — "The Proof Lab"

Status: draft for review, 2026-11-22. Not yet implemented.

## Diagnosis

The current page is a well-written technical document wearing a dark theme. Its strongest
assets — the live ratchet data, the Z3 obligation states, the per-crate proof sources — are
presented as static reading material. A frontier-lab page should feel like an *instrument
panel for a running experiment*: everything live, everything traceable, the visitor touching
the proof machinery within ten seconds.

Concrete problems today:

1. The interactive elements (obligation states, crate proof picker, counterexample viewer)
   are buried mid-page inside a two-column prose layout.
2. Numbers appear in prose, tiles, tables, and footer with no visual hierarchy telling you
   which are live telemetry vs. fixed claims.
3. The CVE baseline — the emotional hook — is a collapsed appendix at the bottom.
4. The architecture diagram is a static picture of the project's most important idea
   (proved kernel vs. disposable renderers).
5. Sections are ordered for a reader, not a visitor: Proof → Arch → Ledger → Scope → CVEs.

## Concept

One page, three altitudes:

- **TL;DR band** (hero + live ticker): what we prove, that it's green right now, one click
  to the machinery.
- **The bench** (centerpiece): an interactive proof workbench the visitor operates.
- **The record** (ledger, CVE baseline, scope): the auditable evidence underneath.

## Proposed structure

1. **Hero** — keep headline and frosted-glass backdrop. Replace prose paragraph with a
   single sentence plus the live status line ("11 crates · 4,102 proof obligations ·
   0 trusted items · re-verified 122s · green").
2. **Live ticker strip** — keep the four StatTiles; add a subtle "last verified" timestamp
   and commit digest already available in `ratchet.json`. All tiles keep the existing
   `not recorded` behavior on missing data (Law 2: no placeholders, ever).
3. **The Bench (new centerpiece, moved up to second position)** — merge today's
   "Obligation states" and "Live crate proofs" tabs into one workbench with three modes:
   - *Break it*: the counterexample flow — visitor introduces the typo, watches Z3 return
     SAT with the concrete breaking input in the inlay table, then re-verifies to UNSAT.
     This is the single most persuasive interaction on the page; it should be the default
     view, not one of four state buttons.
   - *Inspect it*: the current 11-crate live source browser, upgraded with syntax
     highlighting and deep links into GitHub.
   - *Obligations*: the four-state explainer (verified / counterexample / timeout / admit)
     retained as the educational layer.
4. **Architecture, interactive** — one clean drafting-style diagram of the kernel/renderer
   boundary. Detail is *progressively disclosed*: the drawing carries no visible labels
   beyond the two or three names that orient you; hovering or tapping a boundary reveals
   the theorem that guards it (e.g. the WebIDL boundary surfaces
   `theorem_use_after_revoke_and_realloc_rejected`; the Wasm sandbox surfaces
   `theorem_wasm_invoke_sandbox_containment`). Design-only components (kernel, Nanvix,
   HTML/CSS) are drawn hatched/outline so proved vs. planned reads at a glance —
   honest by construction.
5. **Crate ledger** — keep the table; make rows expandable to per-crate detail (verified
   fns, verify seconds, test counts, key theorems) from `ratchet.json`.
6. **CVE baseline as a single drafter's exhibit, not an appendix** — the 20 exploited
   Chrome zero-days drawn as one quiet dimensioned timeline grouped by violated assumption
   (type confusion, OOB, lifetime). No per-node labels by default; selecting a group
   reveals the crate/theorem class that closes that hole. Move it up; it's the "why" that
   earns the visitor's attention for everything below.
7. **Scope & tradeoffs** — keep, condensed; honest limits (vurl coverage, fuel semantics,
   i64-IR simulation scope, design-only kernel) as a visible "known unknowns" card. A lab
   page that hides its limits is marketing.

## Design language — craftsman drafter, modern and restrained

Direction from review: a master drafter's drawing board — precise, hand-finished, calm —
rendered in modern futuristic color, never neon. The page teaches one very technical idea;
nothing on it may compete with that idea for attention.

- **Drafting craft**: hairline rules, exact registration, aligned baselines, dimension-line
  motifs (tick marks, thin leaders) used sparingly to point at the *one* thing a section is
  about. Diagrams look drawn, not generated: consistent 1px strokes, real geometry, no
  drop-shadow confetti.
- **Color**: deep graphite/ink ground; a single restrained futuristic accent (a muted
  electric teal or cool phosphor green — desaturated, ~60–70% chroma, not neon) reserved
  exclusively for live-verified status and primary interaction. Amber/red only for
  warn/fail. Everything else is ink and paper tones. "Accent = proved" becomes a page-wide
  reflex because nothing else is allowed to glow.
- **Elevation, with intent**: real but quiet depth on interactive controls only — the bench
  panel, CTAs, expandable rows sit one layer above the page (soft 1–2px umbra, subtle top
  highlight, like a machined plate on a drawing board). Static prose and diagrams stay flat
  on the paper. Elevation signals "you can touch this"; flat signals "read this".
- **Typography**: JetBrains Mono for telemetry, code, and digests; a crisp grotesque for
  the few headings; generous line-height in the little prose that remains.
- **Radical label discipline**: every label on the page must justify its existence. One
  concept per section, one sentence of framing, the artifact does the talking. No
  triple-labeling, no caption stacking, no badge soup. If a control needs a paragraph to
  explain it, the control is wrong. Target: a first-time visitor can name what the project
  does after one screenful, without reading a second label.
- Respect `prefers-reduced-motion`; no scroll-jacking, no autoplay animation.

## Hard constraints (non-negotiable)

- Every number, status, and label is backed by `browser/ratchet.json` or `data/stats.json`
  at runtime; missing data renders `not recorded`. Zero mock, zero estimated, zero fallback
  content anywhere (Constitutional Law 2).
- Playwright suite (`tests/site.spec.js`) extended to exercise every new interactive
  control against the real JSON before anything ships (Law: no completion claims on
  compilation alone).
- GitHub Pages static hosting only: no backend, no client-side secrets, build stays
  `npm run build` → `dist/`.

## Phasing

1. **P0** — done: fix obligation-pane grid bug (a125637).
2. **P1** — restructure the bench (modes 1–3) and move it to position 2; default to the
   counterexample flow.
3. **P2** — CVE timeline; interactive architecture with theorem tooltips + proved/planned
   hatching.
4. **P3** — expandable ledger rows, ticker timestamps, syntax highlighting, motion pass.
5. Each phase ships with its Playwright coverage; CI re-verifies proofs before deploy
   (already in place).
