# CONDUIT Lab — Nanvix × Verus

GitHub Pages site presenting the Verus verification topology of the Nanvix sandbox.

- Static HTML/CSS/JS with a locally vendored Three.js — no build step and no CDN dependency.
- Interactive 3D globe: each island is a major Nanvix component, colored by verification status.
- Rehoboam-style disturbance rings with projected callouts and leader lines.
- The browser engine (Parawing) is the active frontier, marked with a violet outline.
- `assets/conduit-banner-v2.jpg` is the central CONDUIT identity artwork.
- Published from `main` via GitHub Pages.

## Local preview

```sh
python3 -m http.server 8000
# open http://localhost:8000
```
