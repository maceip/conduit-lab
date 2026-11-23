# The Drawing Standard

**CONDUIT Lab · atelier** — the rules for adding an icon or a plate that matches the
existing set.

The reference implementation lives in `atelier/src/illustration/`. The published engine
this package was ported from is `v8-iso/iso-cad.mjs` — **read-only reference, never
modify it**. Every value below is taken from the code, not from the design spec; where
the two disagree, this document wins.

Scope: the illustration package (icons and plates) and the board they are drawn on. The
tier-1 statistics components in `atelier/src/viz/stats/` follow the same palette,
stroke and motion grammar but are not drawings and are not covered here.

---

## 1. The palette

All colour comes from `atelier/src/contract/tokens.ts`. **Never hardcode a hex** — not
in a component, not in a test, not in a stylesheet.

### Board and ink

| Token | Value | Use |
| --- | --- | --- |
| `BOARD.page` | `#0c0d0e` | Board ground behind everything |
| `BOARD.plate` | `#141516` | Plate panel, balloon fill |
| `BOARD.raised` | `#1a1d20` | Raised panel |
| `BOARD.line` | `#586068` | Structural edges, centrelines, dimension lines, band rules |
| `BOARD.rib` | `#2e3338` | Hidden edges, panel borders, list dividers |
| `BOARD.edgeHi` | `#b2b8be` | Neutral-tone edge highlight |
| `BOARD.ink` | `#8a9096` | Labels, captions, part names, hatch ink |
| `BOARD.inkHi` | `#e8ecee` | Primary text |
| `BOARD.live` | `#f4f6f7` | Leader terminal dot, focus outline |
| `BOARD.accent` | `#74c7b0` | **Reserved — live-verified status only** |
| `BOARD.warn` | `#d9a441` | **Reserved — failure path only** |
| `BOARD.fail` | `#d4645c` | **Reserved — failure path only** |

### The status rule

`BOARD.accent` is not a decoration colour. It means **this is live-verified** — a part
that is proven by a run, not asserted by a drawing. Amber and red are failure paths:
amber for a warning, red for a violation. A drawing that is merely "important" gets
`hi` or `body`, never the accent.

The `Tone` type (`'proved' | 'warn' | 'fail' | 'neutral'`) is the **only** way status
reaches a drawing, and it drives exactly one thing — the edge/mark colour:

| Tone | Colour | Meaning |
| --- | --- | --- |
| `proved` | `BOARD.accent` | Live-verified |
| `warn` | `BOARD.warn` | Failure path, warning |
| `fail` | `BOARD.fail` | Failure path, violation |
| `neutral` | `BOARD.edgeHi` (edges) / `BOARD.ink` (cut edges) | No status |

A cut edge is drawn in `BOARD.ink` when the tone is neutral, because a light line
would vanish into the bright cut face it is meant to define.

---

## 2. The stroke table

Every stroked element in a drawing carries `vector-effect="non-scaling-stroke"`, and
the drawing group carries `stroke-linecap="round"` and `stroke-linejoin="round"`.
Cap and join are inherited, so they are set once on the group; `vector-effect` is
**not** inherited and must be on each element.

| Role | Width | Dash | Colour |
| --- | --- | --- | --- |
| Structural edge | `STROKE.structure` = 1.05 | — | `BOARD.line` |
| Cut edge | `STROKE.cutEdge` = 1.35 | — | `BOARD.ink`, or the tone colour |
| Hidden edge | `STROKE.hidden` = 0.75 | `DASH.hidden` = `2.5 2` | `BOARD.rib` |
| Centreline | `STROKE.centerline` = 0.6 | `DASH.centerline` = `8 2 1.6 2` | `BOARD.line` |
| Section hatch | `STROKE.hatch` = 0.5 | — | `BOARD.ink` at 0.55 opacity |
| Leader | `STROKE.leader` = 0.9 | `DASH.hidden` = `2.5 2` | `BOARD.line` |
| Face outline | `STROKE.hatch` = 0.5 | — | the face's own ramp colour |

The face outline is filled **and** stroked with the same ramp colour, so the silhouette
is carried by the fill, not by a contrasting outline.

Two notes on the port:

- The published engine strokes faces at `0.55`; the atelier uses `0.5` (`STROKE.hatch`,
  which therefore does double duty as the face-outline weight). The difference is
  invisible at plate scale, but do not "fix" it by inventing a new token.
- The leader's dash pattern is the hidden-edge pattern. That is deliberate: a leader is
  a hidden reference, not a visible edge.

---

## 3. The nine anatomy rules

**MANDATORY** means a drawing that breaks it is wrong and will be rejected.
**DESIRABLE** means use it where it carries information.

1. **Exploded separation along one dominant axis** — MANDATORY.
   Every assembly declares one `axis` and every part's `explode` vector is authored
   parallel to it. The explode distance is the vector's component along the axis,
   scaled by the assembly's `explodeScale`; a perpendicular component is carried
   through unchanged so a diagonal explode still reads. One axis per assembly, always.

2. **Hairline leader lines with a terminal dot** — MANDATORY.
   A leader runs from the part's own surface out to its balloon. The polyline has one
   orthogonal elbow, so the run leaves the drawing along an axis and never turns
   through an arbitrary angle. A 2px `BOARD.live` dot marks the anchor end.

3. **Circled part numbers** — MANDATORY.
   Balloons are `r = 9` circles, one stroke, numeral centred in 9px mono, 10px clear
   of the drawing bounds, spaced at least 24px centre-to-centre so two never overlap.
   Number them in assembly order and map each to the parts list. The balloon sits on
   the side of the drawing with the most room, so the leader takes the shortest run.

4. **45°/135° opposed section hatching** — MANDATORY.
   Every cut face is hatched at 45°; **adjacent sectioned parts hatch in opposite
   directions** so two neighbouring cuts never read as one. The pattern index's parity
   picks the direction. The hatch is applied with `patternTransform`, which fixes it to
   the drawing plane rather than to the part — exactly how a drafted section reads.
   Tile size 6 user units.

5. **Dash-dot centrelines** — MANDATORY.
   A centreline runs through every axis of symmetry and overshoots the feature by 3%
   at each end.

6. **Dimension lines with terminators** — DESIRABLE.
   Extension lines from the feature, a dimension line 18 units off it, 45° slash
   terminators 6 units long, and a mono value label. Use it where there is a real
   dimension to state; do not invent dimensions to fill a plate.

7. **The parts list** — MANDATORY for plates, DESIRABLE for icons.
   A hairline-ruled table of balloon number, part name and count. Parts without a
   balloon are not listed. Icons set `partsList: false`; the plate's list is the
   reference. No quantities beyond the count and no dimensions — that is `inkwork`'s
   territory, not this engine's.

8. **Consistent projection** — MANDATORY.
   Every drawing uses the same camera. See §4.

9. **Hairline / no-shadow discipline** — MANDATORY.
   No drop shadows. No gradients used as pseudo-shadow. Depth comes from the face
   shading ramp and from stroke weight alone. A face that needs to recede gets a
   darker ramp index, not a blur.

---

## 4. The projection convention

**Azimuth 42°, elevation 30°** — the `ISO` token in `contract/tokens.ts`, and the
default of `createCad` in `v8-iso/iso-cad.mjs` (`azDeg = 42, elDeg = 30`).

The camera basis and the key light are a verbatim port:

```
az = azDeg * PI/180,  el = elDeg * PI/180
V  = [cos(el)cos(az), cos(el)sin(az), sin(el)]     // view direction
Rx = [sin(az), -cos(az), 0]                       // screen right
Ds = [sin(el)cos(az), sin(el)sin(az), -cos(el)]    // screen down
project(p) = [dot(p, Rx), dot(p, Ds)]
L  = normalize([cos(az-0.55)*0.48, sin(az-0.55)*0.48, 0.88])
```

**Why it matters:** because the published figures and the atelier figures share the
basis *and* the light, the same part with the same normal lands on the same ramp index
in both. Change the camera and the two sets stop reading as one set. The camera is not
a style choice, it is the contract with `v8-iso/`.

Two more ported constants:

- **Crease angle 34°** — above this, an edge is drawn as a contour.
- **Edge depth bias 0.12** — the drawn edge sits this far in front of its face.

Shading is computed against the **world** normal and the world key light, before the
view transform — the same order the published engine uses. Do not shade in view space.

---

## 5. The per-part body palette

**This is the rule people get wrong. Read it twice.**

The published plates in `v8-iso/` are **not** drawn on one ramp. Each part selects a
palette, and the shading ramp is applied *within* that palette. That is where their
tonal range comes from — a dark skid under a bright machined silo.

### The three ramps

| Palette | Role | Ramp (index 0 → top) | Published custom properties |
| --- | --- | --- | --- |
| `dark` | Understructure: skids, frames, pedestals, pumps | `#0b0c0e` → `#101214` → `#16191c` | `--dk0..--dk2` |
| `body` | The main mass | `#111315` → `#171a1d` → `#1e2226` → `#262b30` | `--bd0..--bd3` |
| `hi` | The prominent machined element | `#8e959c` → `#b2b8be` → `#cfd4d8` → `#e8ecef` | `--hi0..--hi3` |

Access them as `PALETTES.dark` / `PALETTES.body` / `PALETTES.hi`, or `SHADE_DARK` /
`SHADE_BODY` / `SHADE_HI`. The `dark` ramp has three steps; `body` and `hi` have four.

> The ramps are byte-identical to the published custom properties, so an atelier face and
> a published face with the same normal land on the same tone. There is deliberately no
> flat ramp in `tokens.ts` — collapsing every part onto one ramp is what destroys the
> form.

### Classifying a face into a sub-ramp

`b` is the lambert value, `dot(worldNormal, keyLight)`. The thresholds are the
published ones, per palette:

| Palette | Index 3 | Index 2 | Index 1 | Index 0 |
| --- | --- | --- | --- | --- |
| `body` | `b > 0.55` | `b > 0.16` | `b > -0.22` | otherwise |
| `hi` | `b > 0.52` | `b > 0.12` | `b > -0.25` | otherwise |
| `dark` | — | `b > 0.35` | `b > -0.15` | otherwise |

`dark` has no index 3. The implementation is `shadeClassIndex` in
`atelier/src/illustration/engine/shade.ts`; the table above is its `SHADE_CLASS`
constant.

### Cut faces

A cut face is a **bright machined surface**, not a shaded one. It takes `CUT_FACE`
(`#e8ecef`) regardless of the part's palette, and the section hatch is laid **over** it.
The hatch is inked (`BOARD.ink` at 0.55 opacity), not highlighted — a light line would
disappear into the cut.

### Two traps

1. **Never introduce a flat ramp.** `contract/tokens.ts` used to export a six-step
   single ramp called `SHADE`. It was the collapsed ramp that caused the defect below,
   and it has been removed. If you find yourself wanting one ramp for every part, that
   is the bug, not the design. Use `PALETTES`.
2. **The published engine's fourth palette.** `iso-cad.mjs` has a `live` ramp
   (`--hi1..--hi3` with thresholds `b > 0.45` / `b > 0.05`). The atelier deliberately
   drops it: live-verified status is carried by `BOARD.accent` through `Tone`, not by a
   fourth body ramp. Do not reintroduce a `live` palette.

### Why this rule is a hard rule

We found the collapsed-ramp defect by **rendering the atelier output and putting it
side by side with the repo's own published plate**. Every part had been shaded in the
`body` band, so the whole assembly read as flat silhouettes with faint edges, and the
section hatching was the only thing that still read. The published fig-01 skid frame is
`dark`, its pipes are `body`, and its realm silo is `hi` — a bright machined silo.

**Collapsing every part onto one ramp destroys the form.** The regression tests in
`atelier/src/illustration/engine/engine.test.ts` (`describe('palette shading')`) now
guard the thresholds, the per-palette ramp index, the palette travelling onto every
projected face, and the `body` default for an unassigned part. Do not weaken them.

---

## 6. One worked example

`atelier/src/illustration/icons/IsolateIcon.tsx` — `v8::Isolate`, the twin-silo process
skid, ported from `v8-iso/pages/fig-01-isolate.html`.

### The part list and its palettes

| # | Part | Label | Palette | Geometry | Explode | Sectioned |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `skid` | Skid base | `dark` | `box` | — | |
| 2 | `silo-main` | Main silo | `body` | `cyl` | `[0, 0, 52]` | ✓ |
| 3 | `silo-realm` | Realm silo | `hi` | `cyl` | `[0, 0, 104]` | |
| 4 | `manifold` | Process manifold | `hi` | `tube` | `[0, 0, 156]` | |
| 5 | `pump` | Microtask pump | `dark` | `cyl` | `[0, 0, 208]` | |
| 6 | `discharge` | Task discharge | `body` | `cyl` | `[0, 0, 260]` | |
| 7 | `valve` | Locker cam valve | `body` | `cyl` | `[0, 0, 312]` | |

### How to choose a palette

Ask what the part *is* in the assembly, not how important it is:

- It carries the machine or holds the ground → `dark` (skid, pump).
- It is the main mass → `body` (the main silo, the discharge stack).
- It is the one bright machined element the eye should land on → `hi` (the realm silo,
  the manifold that ties the two together).

One or two `hi` parts per assembly. If everything is `hi`, nothing is.

### The pattern to copy

```tsx
import { useId, useMemo } from 'react';
import { projectAssembly, renderPlate, type Assembly } from '../engine';

export const MY_ASSEMBLY: Assembly = {
  azDeg: 42,          // never change these
  elDeg: 30,
  axis: [0, 0, 1],    // one explode axis per assembly
  explodeScale: 1,
  partsList: false,   // icons: false; plates: true
  parts: [
    { id: 'base', label: 'Base', palette: 'dark', balloon: 1,
      geometry: { kind: 'box', at: [0, 0, 0], size: [200, 120, 12] } },
    // ...
  ],
};

export function MyIcon({ size = 32, className, tone = 'neutral', annotated = true, title }: IconProps) {
  const id = useId();                                  // namespaces every SVG defs id
  const plate = useMemo(() => projectAssembly(MY_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
```

A plate is the same, with `partsList: true` and a `caption`
(`{ figure, name, scale, note?, legend? }`).

### Procedure for a new icon

1. Copy the geometry of the subject from its `v8-iso/pages/fig-*.html` figure.
2. Assign each part a palette using the heuristic above, and write one line of prose
   naming which parts are `hi` and which are `dark`.
3. Author `explode` vectors parallel to the assembly `axis`, in assembly order.
4. Mark at least one part `sectioned: true` so the plate carries the hatching cue, and
   give each sectioned part a distinct index so the hatch parity alternates.
5. Number the balloons in assembly order and set `label` on every part.
6. Add `palette` to every part — an unassigned part silently defaults to `body`, which
   is exactly the failure mode the tests exist to catch.
7. Render it and **put it beside the published plate**. If the tone does not read, the
   palette assignment is wrong.

---

## 7. The hard rules

- **No drop shadows. No gradients used as pseudo-shadow.** Depth is the face shading
  ramp plus stroke weight. No `filter:`, no `feDropShadow`, no radial/linear gradient
  standing in for one.
- **Tokens only.** Every colour, stroke width, dash and duration comes from
  `contract/tokens.ts`. No hardcoded hex, in any file, including tests.
- **Namespace every SVG `id`.** React 19's `useId()` supplies the prefix; run it
  through `safeId()` before it goes into a `url(#...)`. Two instances of the same icon
  on one page must never share a hatch pattern id.
- **Accessible names.** Pass `title` and the root becomes `role="img"` with
  `aria-label` and a `<title>` child. With no `title` the SVG is decorative and must
  be `aria-hidden` and `focusable="false"`. Every icon and component has an
  accessible name; decorative SVG is hidden.
- **TypeScript strict.** No `any`, no `@ts-ignore`.
- **The contract is frozen.** `atelier/src/contract/` is read it, never modify it. If
  you need a change there, report it to Chief.
- **Atelier work touches nothing outside `atelier/`.** `site/`, `v8-iso/`, `inkwork/`,
  `browser/`, `data/` and `scripts/` are read-only reference for this work. In
  particular `v8-iso/iso-cad.mjs` is the published engine — never modify it.
- **One writer per path.** Two tasks must never write the same folder at the same
  time.

---

*Sources: `atelier/src/contract/tokens.ts`, `atelier/src/contract/index.ts`,
`atelier/src/illustration/engine/{shade,render,camera,explode,hatch,balloon,leader,dimension,centerline,partsList}.ts`,
`atelier/src/illustration/icons/IsolateIcon.tsx`,
`atelier/src/illustration/plates/V8CorePlate.tsx`, and the read-only reference
`v8-iso/iso-cad.mjs`.*
