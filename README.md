# CONDUIT Lab

A static GitHub Pages site presenting the CONDUIT local formal verification workspace on Apple Silicon.

Every number, version and status on the page is rendered by `app.js` from `data/stats.json`.
Nothing is hard-coded in `index.html`. If `stats.json` is missing, the page shows an error, not numbers.

## Regenerate the data

```sh
source ~/workspaces/verus-stack/env.zsh
python3 scripts/collect_stats.py               # add --with-mathlib to build mathlib benchmarks too
```

The collector re-verifies `vstd` (into a temp dir; installed artifacts are untouched) and the
Verus examples, builds each Vero Lean benchmark, records toolchain versions and repo commits, and saves
raw command output to `data/logs/`. Commit `data/` after each run.

## Test

```sh
npm install
npm test        # Playwright: asserts the page matches data/stats.json
```

## Local preview

```sh
python3 -m http.server 8000   # open http://localhost:8000
```

## Irrigation console

`irrigation.html` is a garden irrigation console. Valve decisions come from `controller/ctl.rs`, a
Verus-verified controller (pump capacity, max run time, tank never underflows). The same file runs:

- on macOS (built by the bridge with the verus-stack toolchain), and
- as a Nanvix guest (`controller/nanvix-guest`, branch `conduit-irrigation` of maceip/nanvix) on a
  Windows 11 machine with WHP, driven over SSH.

```sh
python3 bridge/conduit_bridge.py --nanvix-host user@windows-host   # settings saved to ~/.conduit-lab/
```

Open the page (local or on GitHub Pages) and allow Chrome's local-network prompt. Soil moisture is simulated;
valve state, tank level and delivered water are the controller's real replies.
