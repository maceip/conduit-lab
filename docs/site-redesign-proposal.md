# CONDUIT Pages Redesign Proposal v2 — "The Proof Lab"

Status: draft for review, 2026-11-22. Supersedes v1 (same file, rewritten after design
review). Aesthetic: master drafter's drawing board in restrained futuristic color. One
page, one idea, taught from zero.

## The narrative arc

The page is a three-act lesson, not a brochure:

1. **Learn it** (Feynman / Khan Academy): the simplest possible formally verified program,
   taught by hand on the drawing board, with a working editor the visitor runs themselves.
2. **Face the gap** (state of the art): if this is so good, why is there no verified
   browser kernel? An honest exhibit of what 40 years of verification actually achieved —
   seL4, CompCert, Verdict, Quark — and exactly where the wall is.
3. **Cross it** (what we're doing): CONDUIT's answer — prove the security boundary, crate
   by crate, with the ratchet as living evidence.

Each act is one screenful of calm, nearly label-free content. The visitor who only reads
act 1 still leaves understanding what formal verification *is*.

## Act 1 — Learn it: "Prove, don't test"

The Feynman move: take the smallest program with a real bug class and make the visitor
*feel* the difference between testing and proving.

**The exhibit.** One tiny function — e.g. `fn abs_nonnegative(x: i64) -> i64` or the
percent-encode byte from `vurl` — drawn on the board three ways:

- *The test way*: a handful of input dots on a number line, green where tests sampled.
  Vast unlit space between the dots. Caption-level label only: "tests check here".
- *The proof way*: the same number line fully lit — a hairline dimension bracket spanning
  `-2⁶³ … 2⁶³-1` with a single accent stroke. "proofs check everywhere."
- *The catch*: the honest twist — `i64::MIN` breaks naive `abs`. The visitor watches Z3
  find the one dark point on the line.

**The working editor.** An embedded code panel, editable, with a "Verify" key. This is
real, not simulated: Z3 compiled to WebAssembly runs in the page (z3.wasm, statically
served from `dist/`), so the visitor's edits are checked by the actual solver against
pre-staged SMT-LIB translations of the Verus examples. Three guided steps, Khan-Academy
style:

1. Run the broken version → solver returns the counterexample (`x = -9223372036854775808`)
   shown as a red dimension tick on the number line.
2. The fix is one edit (a `requires x > i64::MIN` precondition, or `x >= 0` return type);
   run again → fully lit line, UNSAT.
3. A free-play step: mutate anything, see SAT/UNSAT/timeout honestly reported.

No accounts, no server: the solver is a static asset; results are computed in the
visitor's browser. If the wasm fails to load, the panel says so explicitly — never a
canned "verified" badge (Law 2).

**The drawing.** An isometric hairline illustration of the pipeline — source → Verus →
Z3 → verdict — rendered as a small drafting plate: 1px strokes, dimension lines, three
labeled parts maximum. It sits beside the editor and lights its verdict block in the
accent color when the visitor runs a check. Drawn, not screenshotted.

## Act 2 — The gap: "Why isn't everything proved?"

One quiet exhibit, drafter-style: a dimensioned timeline/bar chart of verified systems —
seL4 (~8,700 LOC C, ~20 person-years), CompCert, HACL*/EverCrypt, Verdict (X.509), Quark
(browser kernel, 2012) — against the ~36M-line reality of a modern browser. One sentence
of framing, no wall of text. The point lands visually: verification works, but it has
never scaled to a browser's security boundary, and the reasons (spec drift, proof labor,
solver walls, unverifiable GPU/driver stacks) appear as four small annotation cards —
hover for depth, two words by default.

This act is where today's "Prove the security boundary, isolate the rest" section lives,
rewritten to answer the visitor's fresh question instead of defending a claim.

## Act 3 — The crossing: what CONDUIT is doing

- **The strategy drawing**: one isometric plate — proved kernel in front of disposable
  per-site renderers — hatched where components are still design-only (kernel, Nanvix,
  HTML/CSS). Proved vs. planned reads at a glance; hovering a boundary reveals the theorem
  guarding it, on demand only.
- **The bench**: the interactive proof workbench (break-it counterexample flow → live
  11-crate source browser → four obligation states), now the reward for the lesson of
  act 1 — the visitor already knows what UNSAT means when they get here.
- **The ledger**: the 11-crate ratchet table, expandable rows, every number live from
  `browser/ratchet.json`. This is the lab notebook: 4,102 obligations, 0 trusted items,
  122s re-verify, toolchain digests.
- **The CVE baseline**: 20 exploited Chrome zero-days as one dimensioned timeline grouped
  by violated assumption; selecting a group reveals the theorem class that closes it.
  Placed at the end as the stakes recap, or at the top as a cold-open — decide in review.

## Design language — craftsman drafter, restrained futuristic

- **Drafting craft**: hairline rules, exact registration, dimension lines and tick motifs
  pointing at the *one* thing each section teaches. Isometric plates with consistent 1px
  strokes and real geometry. Drawn, never generated-looking.
- **Color**: deep ink/graphite ground; a single desaturated futuristic accent (muted
  phosphor teal/green) reserved for live-verified status and primary interaction. Amber/red
  only for warn/fail. Nothing else glows.
- **Elevation with intent**: quiet machined-plate depth (1–2px umbra, top highlight) on
  interactive controls only — the editor, the bench, expandable rows. Prose and plates stay
  flat on the paper. Raised = touchable; flat = read.
- **Typography**: JetBrains Mono for code, telemetry, digests; a crisp grotesque for the
  few headings; generous measure in the little prose that remains.
- **Label discipline**: one concept per section, one sentence of framing, the artifact
  talks. Progressive disclosure for everything else. A first-time visitor can say what the
  project does after one screenful.
- `prefers-reduced-motion` respected; no scroll-jacking; no autoplay.

## Hard constraints (non-negotiable)

- Every metric, status, and verdict is real: live from `browser/ratchet.json` /
  `data/stats.json`, or computed in-browser by the actual Z3 wasm. Missing data renders
  `not recorded`; a failed solver load renders an explicit error. Zero mock, zero canned
  output (Constitutional Law 2).
- Playwright coverage for every interactive control — including driving the embedded
  solver through break → fix → verify — before any phase ships.
- Static GitHub Pages only: no backend, no secrets; build stays `npm run build` → `dist/`.
  Z3 wasm is a vendored static asset with a pinned version and license note.

## Phasing

1. **P0** — done: obligation-pane grid fix (a125637).
2. **P1** — Act 1: number-line exhibit + isometric pipeline plate + embedded Z3-wasm
   editor with the three guided steps. This is the heart of the redesign.
3. **P2** — Act 2: the gap exhibit (timeline + four annotation cards), rewriting the
   boundary section around it.
4. **P3** — Act 3: strategy plate with hatched design-only components, bench merge,
   expandable ledger, CVE timeline placement decision.
5. Each phase ships with its Playwright coverage; CI re-verifies proofs before deploy
   (already in place).
