# CONDUIT Lab

A GitHub Pages workbench for the **formally verified browser engine** (`browser/`, design in
[`docs/verified-browser-engine.md`](docs/verified-browser-engine.md)), built with the
[`@maceip/ix-workbench-primitives`](https://github.com/maceip/ix-workbench-primitives) design
system (Siemens iX v5 + React 19, Light DOM).

The page is a three-pane view across familiarity levels with formal verification:

1. **01 · What Verus is** — how spec/exec/proof lanes and Z3 obligations work, and how they
   break (failed postcondition with a counterexample, `rlimit` timeout, `admit` escape hatch),
   shown on real `vurl` code.
2. **02 · Why no verified Linux** — seL4 vs Linux scale, the four structural reasons verified
   kernels are rare, and what verification has actually shipped (CompCert, fiat-crypto, HACL*,
   Verdict, Quark, JSCert, Warblre, WasmCert).
3. **03 · Where we are** — the live proof ratchet, the `vurl` obligation DAG, the last 20
   in-the-wild Chrome CVEs mapped to this engine's coverage, the `vjs` J0–J7 plan (honestly
   marked *design*), and the nine tradeoffs the plan makes.

Every metric is fetched at runtime from `browser/ratchet.json` and `data/stats.json`.
Nothing is hard-coded in the app; if a data file is missing, the page shows an error and
"not recorded", not numbers. Playwright asserts the page against both files.

## Build the site

The primitives are consumed **from source** (the package is unpublished on npm). Clone them
next to this repo — `site/vite.config.ts` also accepts a checkout inside the repo, which is
what CI uses:

```sh
git clone https://github.com/maceip/ix-workbench-primitives ../ix-workbench-primitives
npm --prefix site install
npm run build          # vite build -> dist/, then stages data/, ratchet, irrigation demo
```

## Regenerate the data

```sh
source ~/workspaces/verus-stack/env.zsh
python3 scripts/collect_stats.py               # add --with-mathlib to build mathlib benchmarks too
(cd browser && python3 scripts/ratchet.py)     # re-verify vurl, rewrite browser/ratchet.json
```

The collector re-verifies `vstd` (into a temp dir; installed artifacts are untouched) and the
Verus examples, builds each Vero Lean benchmark, records toolchain versions and repo commits, and saves
raw command output to `data/logs/`. Commit `data/` and `browser/ratchet.json` after each run.

## Test

```sh
npm install
npm test        # builds dist/, then Playwright: page must match ratchet.json + stats.json
```

The irrigation tests additionally start a real local bridge (port 8797) and need the
verus-stack toolchain; set `NANVIX_HOST` to also exercise the Nanvix guest.

## Local preview

```sh
npm run build
python3 -m http.server 8000 --directory dist   # open http://localhost:8000
```

## Deployment

`.github/workflows/pages.yml` checks out this repo **and** `maceip/ix-workbench-primitives`,
builds `site/` with Node 20, and uploads `dist/` to GitHub Pages on push to `main`.
Because the primitives are checked out from GitHub, design-system changes must be pushed to
`maceip/ix-workbench-primitives` before they appear in the deployed site.

## Irrigation console

`irrigation.html` is a garden irrigation console (kept as a standalone page, staged into
`dist/` by the build). Valve decisions come from `controller/ctl.rs`, a
Verus-verified controller (pump capacity, max run time, tank never underflows). The same file runs:

- on macOS (built by the bridge with the verus-stack toolchain), and
- as a Nanvix guest (`controller/nanvix-guest`, branch `conduit-irrigation` of maceip/nanvix) on a
  Windows 11 machine with WHP, driven over SSH.

```sh
python3 bridge/conduit_bridge.py --nanvix-host user@windows-host   # settings saved to ~/.conduit-lab/
```

Open the page (local or on GitHub Pages) and allow Chrome's local-network prompt. Soil moisture is simulated;
valve state, tank level and delivered water are the controller's real replies.