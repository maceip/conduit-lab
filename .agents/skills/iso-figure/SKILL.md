---
name: iso-figure
description: Universal 3D Isometric CAD & Interactive Technical Illustration skill (iso-figure v2). Builds self-contained HTML/SVG interactive isometric models of ANY 3D shape — aircraft turbofan jet engines, sculpted cars, naval cruise-ship hulls, and complex industrial machinery — using surfaces of revolution (revolve), multi-station cross-section skinning (loft), arbitrary 2D profile extrusion (extrudePoly), parallel-transport swept tubes (sweepTube), true silhouette/crease contour extraction, back-to-front depth sorting, clickable 3D parts, and live drag-to-orbit.
---

# Universal 3D Isometric Figure (`iso-figure` v2 — `iso-cad`)

Produces a single self-contained HTML file (zero external libraries, runs directly from disk or embedded iframe) displaying a technical-drafting isometric plate (`Fig N`, title, hint, live state readout) whose 3D geometry goes far beyond boxes: **aerospace turbines, automotive coachwork, marine hulls, conical bowls, helical ramps, gears, C-frames, and piped industrial skids**.

## Why v1 (`box()` only) failed on real machines & vehicles

A 15-line `box(x,y,z,w,d,h)` kernel can draw a pocket calculator or keyboard, because those objects *are* rectangular slabs with rectangular keys. When applied to engines, vehicles, vessels, or industrial machinery, `box()` forces cylinders, bowls, cowlings, hulls, and drums into axis-aligned shoeboxes—making every illustration look like the same rectangular slab.

`iso-cad` (`/Users/mac/conduit-lab/v8-iso/iso-cad.mjs`) replaces box-only composition with a ~260-line dependency-free **3D Parametric Surface & Silhouette CAD Kernel**:

1. **Exact Orthonormal 3D Camera (`azDeg`, `elDeg`) + 4×4 Transform Stack (`push`, `pop`, `mTrans`, `mRotX/Y/Z`, `mScale`)**:
   - Place tilted windshields, raked ship funnels, pitched turbine blades, angled trestles, and steered wheels in local coordinates.
   - Includes built-in **drag-to-orbit** (drag background or press `[` / `]` to orbit in 3D; double-click to reset).
2. **Five Universal Solid & Surface Builders**:
   - `revolve(profile, { axis, origin, segs, a0, a1, cutCaps, ribRings, doubleSided })`: Surfaces of revolution along `x`, `y`, or `z`—jet nacelles (with partial cutaway angles `a0..a1`), spinners, compressor drums, conical bowls, domed pressure silos, nozzles.
   - `loft(stations, { closed, capStart, capEnd, ribStations })`: Multi-station 3D cross-section skinning—automotive bodies, bulbous-bow to cruiser-stern ship hulls, aircraft fuselages, Y-chutes, transition hoppers.
   - `extrudePoly(pts2D, { origin, uAxis, vAxis, wAxis, depth, taper })`: Ear-clipped extrusion of any concave or convex 2D profile—C-frame presses, twisted airfoil blades, involute gears (`gear2D`), stadium conveyor belts (`stadium2D`), stepped promenade decks, cantilevered bridge wings.
   - `cyl(p0, p1, r0, r1, { segs, holeR, ribEvery })`: Arbitrary `p0 → p1` cylinders, cones, frustums, hollow pipes, tires, wheel rims, and rings.
   - `sweepTube(path3D, radius, { cornerR, segs, closed })` + `helix3D(...)`: Parallel-transport 3D swept pipes, fuel manifolds, handrails, coil springs, and spiral feeder ramps with automatic quadratic corner filleting.
3. **True Silhouette & Mechanical Crease Extraction (Zero Mesh Wireframe Slop)**:
   - Smooth curved surfaces never draw internal tessellation facets.
   - `addMesh` builds a topological edge table and strokes an edge **only** when it is a **true horizon silhouette** (one adjacent face faces the camera and the other faces away), an **open rim**, or a **sharp mechanical crease** (`dot(n1, n2) < cos(creaseDeg)`).
   - Every polygon and contour edge enters a **single unified 3D depth-sorted painter list**, so foreground cowlings, fenders, and bridge wings cleanly occlude background silhouettes without x-ray bleed-through.
4. **Zero Shared Floor-Slab / Keypad Chrome**:
   - Never put unrelated objects onto a generic rectangular base slab with a front row of rectangular buttons and a rear LCD box.
   - Let each object stand on its own true physical supports (pylon, tires, waterline/hull, I-beam skid, spring feet, trestle legs).
   - Tag interactive 3D sub-assemblies directly (`{ key: 'actionId' }`) and anchor crisp hairline technical callouts (`cad.callout(pt3, dx, dy, 'LABEL', { key, op, sel })`) to the actual moving parts.

## Recipe Guide by Subject Class

| Subject | Primary Primitives |
|---|---|
| **Aircraft Turbofan Engine** | `revolve` cutaway bypass nacelle (`a0..a1`, `cutCaps: true`), `revolve` nose spinner + core compressor/combustor/exhaust cones, radial loop of `extrudePoly` pitched fan/turbine airfoil blades (`mRotX`), `sweepTube` external fuel/bleed manifolds, translating thrust-reverser sleeve. |
| **Sculpted Car / Coupe** | `loft` 10–12 transverse cross-sections (`[bottom, rocker, fender, beltline, hoodcenter]`) from front splitter to rear diffuser, `loft` `glass: true` fastback cabin greenhouse, 4× `cyl(..., { holeR })` tires + spoke wheels in recessed wheel arches (`mRotZ(steer)`), `extrudePoly` active rear wing. |
| **Cruise Ship / Vessel** | `loft` naval station sections from forward underwater bulbous bow + flared V-stem through flat-bottom midship to cruiser stern, stacked `extrudePoly` rounded-prow terraced balcony decks, cantilevered `extrudePoly` navigation bridge wings, raked `extrudePoly` winged funnel, `cyl` + propeller azimuth pods. |
| **Industrial / V8 Subsystems** | Match the real mechanism's geometry: cylindrical motors with radial cooling fins + `gear2D` pinions, `revolve` open conical vibratory bowls with `helix3D` spiral tracks, `extrudePoly` swan-neck C-frame presses with `revolve` rotary turrets, `stadium2D` conveyor belts around `cyl` rollers. |

## Verification Checklist

1. Build via Node (`writeCadFigure` from `/Users/mac/conduit-lab/v8-iso/iso-cad.mjs`).
2. Capture headless Chrome screenshots at 2× DPI and inspect every silhouette:
   - From 3 meters away, could you mistake any two figures for one another? If yes, eliminate shared slabs/boxes.
   - Are curved surfaces smooth with clean outer silhouettes (zero triangle mesh clutter)?
   - Does orbiting (`[` / `]` or pointer drag) preserve clean occlusion from multiple angles?
   - Does clicking every `[data-k]` part/callout deterministically update both the 3D mechanism and `#readout`?
