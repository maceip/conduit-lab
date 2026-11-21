# CONDUIT Lab: a browser engine we can prove, one component at a time

Of the last 20 Chrome bugs that Google confirmed were exploited in the wild, 13 were in V8.
Most are type confusion or out-of-bounds access, where the JavaScript engine assumed something
about an object's layout that an attacker could make false. This repository is building a browser
in which the security-critical code is checked against its published standard by a theorem prover.
Every unproved line is counted as trusted, and that count is supposed to shrink release by release.

The tool is [Verus](https://github.com/verus-lang/verus). You write Rust plus a specification,
also in Rust, and Verus asks the Z3 solver whether any input breaks the specification. A "no"
from Z3 means the claim holds for every input. A "yes" comes with the input that breaks it.

## What exists today

`browser/url` (crate `vurl`) implements these algorithms from the
[WHATWG URL standard](https://url.spec.whatwg.org/), pinned to commit `4f461b81`:

| Module | Algorithm | Proved |
|---|---|---|
| `percent` | percent-encode and percent-decode, all eight encode sets | exec equals the spec transcription; decode inverts encode exactly when the set contains `%` |
| `ipv4` | IPv4 parser, including hex, octal and the ends-in-a-number check | exec equals the spec |
| `ipv6` | IPv6 parser (with `::` compression and embedded IPv4) and serializer | exec equals the spec for both |

Each spec loop is its own recursive spec function, and the Rust code is proved equal to it loop
for loop. The crate is `#![forbid(unsafe_code)]` and has no `assume`, `admit` or `external_body`.
The proofs are backed by WPT `urltestdata.json` cases and by randomized differential tests against
the `url` and `percent-encoding` crates. Current counts (verified functions, trusted items, seconds
to verify, tests) are in [`browser/ratchet.json`](browser/ratchet.json), which
`browser/scripts/ratchet.py` writes from a real run.

vurl does not yet cover validation errors, opaque or domain hosts, IDNA, or the main URL parser
state machine. Proving that the IPv6 serializer output parses back to the same address is done by
tests only.

## What is still design

[`docs/verified-browser-engine.md`](docs/verified-browser-engine.md) is the plan. It is modeled on
Verdict, a verified X.509 validator in Verus, and on Quark, a 2012 browser whose kernel was proved
in Coq while unmodified WebKit ran untrusted in sandboxed tabs. A kernel written in Verus owns the
network parsers, origin and cookie policy, tabs and the address bar. Renderers run one per site in
a sandbox and can only act through typed IPC. The JavaScript engine, `vjs`, is a safe-Rust
interpreter with no JIT. Its top-level theorem is that a run returns the spec's answer, runs out of
fuel, or refuses with an explicit `Unsupported(feature)`.
[`docs/vjs-plan-review.md`](docs/vjs-plan-review.md) maps the 20 CVEs above onto that design and
lists what it gives up.

None of the kernel, `vjs` or the Nanvix renderer isolation is code yet. Until it is, the plan's
protection against V8-class bugs is a sandbox nobody has proved, which is where Chrome is today.

## The site

The GitHub Pages site (`site/`, React 19 on
[`@maceip/ix-workbench-primitives`](https://github.com/maceip/ix-workbench-primitives), Siemens iX v5)
tells the same story in five sections: the exploited CVEs and the answer to each, what a Verus
proof checks (shown on real vurl code), why nobody proves a whole browser or a whole Linux, the
kernel-and-renderers design, and status. It reads every number at load time from
`browser/ratchet.json` and `data/stats.json`. If either file is missing, it shows an error and
"not recorded". Playwright checks the rendered page against both files.

### Build

The primitives are used from source because the package is not on npm. Clone them next to this
repo. `site/vite.config.ts` also accepts a checkout inside the repo, which is what CI uses.

```sh
git clone https://github.com/maceip/ix-workbench-primitives ../ix-workbench-primitives
npm --prefix site install
npm run build          # vite build -> dist/, then stages data/, ratchet, irrigation demo
```

### Regenerate the data

```sh
source ~/workspaces/verus-stack/env.zsh
python3 scripts/collect_stats.py               # add --with-mathlib to build mathlib benchmarks too
(cd browser && python3 scripts/ratchet.py)     # re-verify vurl, rewrite browser/ratchet.json
```

The collector re-verifies `vstd` into a temp dir (installed artifacts are untouched) along with
the Verus examples, builds each Vero Lean benchmark, records toolchain versions and repo commits,
and saves raw command output to `data/logs/`. Commit `data/` and `browser/ratchet.json` after each run.

### Test

```sh
npm install
npm test        # builds dist/, then Playwright: page must match ratchet.json + stats.json
```

The irrigation tests also start a real local bridge on port 8797 and need the verus-stack
toolchain. Set `NANVIX_HOST` to exercise the Nanvix guest too.

### Local preview

```sh
npm run build
python3 -m http.server 8000 --directory dist   # open http://localhost:8000
```

### Deployment

On push to `main`, `.github/workflows/pages.yml` checks out this repo and
`maceip/ix-workbench-primitives`, builds `site/` with Node 20, and uploads `dist/` to GitHub Pages.
Design-system changes only reach the deployed site after they are pushed to
`maceip/ix-workbench-primitives`.

## Irrigation console

`irrigation.html` is a standalone page that the build copies into `dist/`. It is a garden
irrigation console whose valve decisions come from `controller/ctl.rs`, a Verus-verified controller
(pump capacity, maximum run time, and a tank that never underflows). The same file runs in two
places: on macOS, built by the bridge with the verus-stack toolchain, and as a Nanvix guest
(`controller/nanvix-guest`, branch `conduit-irrigation` of maceip/nanvix) on a Windows 11 machine
with WHP, driven over SSH.

```sh
python3 bridge/conduit_bridge.py --nanvix-host user@windows-host   # settings saved to ~/.conduit-lab/
```

Open the page locally or on GitHub Pages and allow Chrome's local-network prompt. Soil moisture is
simulated. Valve state, tank level and delivered water are the controller's real replies.
