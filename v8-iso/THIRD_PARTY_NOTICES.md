# Third-Party Notices (`v8-iso/`)

The interactive isometric V8 component figures in this directory are built using two open-source isometric illustration methodologies and kits:

1. **Anatomy** — <https://github.com/wheresryan22/anatomy> (MIT License)
   - Used for the 5 benchtop mechanical V8 component rigs (`v8-iso/anatomy/`), four-tone solid shading (`v8-iso/kit/iso-kit.mjs`, `lathe.mjs`, `tube.mjs`), 3D geometry & painter's-order audit (`v8-iso/kit/audit.mjs`), and line-end verification.

2. **ai-iso-skill (`iso-figure`)** — <https://github.com/MrBongoC/ai-iso-skill> (MIT License)
   - Used for the 5 pressable isometric V8 component consoles (`v8-iso/iso-figure/`), using the 15-line `TOP` / `FRONT` / `SIDE` SVG `matrix()` plane projection kernel, non-scaling hairline strokes, and tactile `.press` state machines.
