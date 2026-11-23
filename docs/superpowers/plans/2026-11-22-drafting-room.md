# The Drafting Room — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build an isolated `atelier/` React 19 workspace containing 8 exploded-isometric SVG icons, 2 large cutaway plates, a tiered visualization component library (animated stats, interactive 3D, algorithm scenes), and a gallery — without touching `site/`.

**Architecture:** Chief owns a frozen shared surface (`atelier/src/contract/**`) plus the app scaffold. Four member bots own strictly disjoint feature folders and build against the frozen contract. Chief integrates and verifies. The illustration engine is a port-and-extend of `v8-iso/iso-cad.mjs` (adds section hatching, balloons, explode offsets, centerlines, dimension lines, parts list).

**Tech Stack:** React 19, TypeScript 5.7 strict, Vite 6, Vitest 3, Playwright 1.65, `three` 0.170 (Tier 2 only). All versions align with existing repo deps (`site/` React 19 + Vite 6 + TS 5.7; `inkwork/` three 0.170 + vitest 3.2.4; root `@playwright/test` 1.65.1).

**Spec:** `docs/superpowers/specs/2026-11-22-drafting-room-design.md` (commit `a17270d`). This plan is its executable form.

## Global Constraints

- **Nothing outside `atelier/` may be created or modified.** `git diff --stat -- site/ v8-iso/ inkwork/ browser/ data/` must be empty at the end. This is non-negotiable (spec N1, N4).
- **No mock data.** Metrics render from `browser/ratchet.json` and `data/stats.json`, or are computed in-browser. Missing data renders `not recorded`. Never a canned value (spec N2, Constitutional Law 2).
- **Dark drafter board only.** No light/paper theme in Phase 1 (spec N3).
- **Dependencies allowed in `atelier/`:** `react`, `react-dom`, `three` (runtime); `@types/react`, `@types/react-dom`, `@types/three`, `@vitejs/plugin-react`, `@playwright/test`, `typescript`, `vite`, `vitest`, `jsdom` (dev). Nothing else.
- **Do NOT use `@react-three/fiber`.** R3F v8 pins React 18; the atelier app is React 19. Use raw `three` inside a React wrapper. `inkwork/` uses R3F v8 and is reference-only (spec 6.4).
- **Palette is fixed.** Use `atelier/src/contract/tokens.ts` values verbatim. Never hardcode a hex in a component file — import the token.
- **Accent (`--accent`, phosphor teal) is reserved** for live-verified status. Amber/red only on failure paths.
- **No drop shadows, no gradient fills used as pseudo-shadow.** Depth = face shading ramp + stroke weight. Exception: 1–2px umbra on interactive controls only.
- **All strokes** use `vector-effect: non-scaling-stroke`, `stroke-linecap: round`, `stroke-linejoin: round`.
- **`prefers-reduced-motion: reduce`** must render final state instantly. Hard requirement, Playwright-tested.
- **TypeScript `strict`** on. No `any`, no `@ts-ignore`, no `as unknown as` escapes in public API.
- **File ownership is disjoint.** No two workers write the same file. If you need something outside your folder, request it from Chief — do not edit it.

---

## File Structure

```
atelier/
  package.json                      # scaffold (Task 0)
  vite.config.ts                    # scaffold (Task 0)
  vitest.config.ts                  # scaffold (Task 0)
  tsconfig.json                     # scaffold (Task 0)
  index.html                        # scaffold (Task 0)
  playwright.config.ts              # scaffold (Task 0)
  src/
    main.tsx                        # scaffold (Task 0)
    App.tsx                         # scaffold (Task 0) — gallery shell
    contract/
      index.ts                      # scaffold (Task 0) — frozen public types
      tokens.ts                     # scaffold (Task 0) — palette/stroke/motion
      motion.tsx                    # scaffold (Task 0) — reduced-motion provider
    illustration/
      engine/
        camera.ts                   # Task 1 — isometric projection
        geometry.ts                 # Task 1 — GeometrySpec -> faces
        shade.ts                    # Task 1 — normal -> shade ramp
        hatch.ts                    # Task 1 — section hatch patterns
        balloon.ts                  # Task 1 — numbered balloons
        leader.ts                   # Task 1 — leader lines + labels
        dimension.ts                # Task 1 — dimension lines
        centerline.ts               # Task 1 — dash-dot centerlines
        explode.ts                  # Task 1 — exploded-axis offsets
        partsList.ts                # Task 1 — BOM table
        render.ts                   # Task 1 — compose a Part[] -> SVG
        index.ts                    # Task 1 — public engine API
      icons/
        IsolateIcon.tsx             # Task 2
        PointerTaggingIcon.tsx      # Task 2
        HiddenClassesIcon.tsx       # Task 2
        ParserIcon.tsx              # Task 2
        IgnitionIcon.tsx            # Task 2
        OldSpaceIcon.tsx            # Task 2
        NewSpaceIcon.tsx            # Task 2
        RatchetIcon.tsx             # Task 2
        index.ts                    # Task 2 — barrel
      plates/
        V8CorePlate.tsx             # Task 3
        KernelRendererPlate.tsx     # Task 3
        index.ts                    # Task 3 — barrel
    viz/
      stats/
        CountFigure.tsx             # Task 4
        OdometerReels.tsx           # Task 4
        StatTile.tsx                # Task 4
        SplitBar.tsx                # Task 4
        RadialGauge.tsx             # Task 4
        DeltaChip.tsx               # Task 4
        RatchetCounter.tsx          # Task 5
        index.ts                    # Task 4
      stage/
        GcHeapScene.tsx             # Task 6
        threeScene.ts               # Task 6
        PrattParserScene.tsx        # Task 7
        TriColorGcScene.tsx         # Task 7
        stepper.ts                  # Task 7 — shared stepper machinery
        index.ts                    # Task 6
    gallery/
      Gallery.tsx                   # Task 8
      GalleryNav.tsx                # Task 8
      IconSheet.tsx                 # Task 8
      PlateSheet.tsx                # Task 8
      StatsSheet.tsx                # Task 8
      SceneSheet.tsx                # Task 8
      gallery.css                   # Task 8
  tests/
    setup.ts                        # Task 0
    illustration.test.tsx           # Task 8
    stats.test.tsx                  # Task 8
    scene.test.tsx                  # Task 8
    reduced-motion.spec.ts          # Task 8
    atelier.spec.ts                 # Task 8
```

---

### Task 0: Scaffold the isolated atelier workspace (Chief, pre-dispatch)

MCode writes this before the team is created so no two bots ever contend for a shared file.
Chief owns it thereafter and may amend the contract only with MCode's approval.

**Files:**
- Create: `atelier/package.json`, `atelier/vite.config.ts`, `atelier/vitest.config.ts`, `atelier/tsconfig.json`, `atelier/index.html`, `atelier/playwright.config.ts`
- Create: `atelier/src/main.tsx`, `atelier/src/App.tsx`
- Create: `atelier/src/contract/index.ts`, `atelier/src/contract/tokens.ts`, `atelier/src/contract/motion.tsx`
- Create: `atelier/tests/setup.ts`

- [ ] **Step 1: Write `atelier/package.json`**

```json
{
  "name": "conduit-atelier",
  "private": true,
  "version": "0.1.0",
  "type": "module",
  "description": "Isolated drafting-room workspace for CONDUIT Lab icons, plates and visualization components. Not wired into the site.",
  "scripts": {
    "dev": "vite",
    "build": "tsc --noEmit && vite build",
    "preview": "vite preview",
    "typecheck": "tsc --noEmit",
    "test": "vitest run",
    "test:watch": "vitest",
    "test:e2e": "playwright test"
  },
  "dependencies": {
    "react": "^19.0.0",
    "react-dom": "^19.0.0",
    "three": "^0.170.0"
  },
  "devDependencies": {
    "@playwright/test": "^1.65.1",
    "@types/react": "^19.0.0",
    "@types/react-dom": "^19.0.0",
    "@types/three": "^0.170.0",
    "@vitejs/plugin-react": "^4.3.4",
    "jsdom": "^25.0.1",
    "typescript": "^5.7.2",
    "vite": "^6.0.0",
    "vitest": "^3.2.4"
  }
}
```

- [ ] **Step 2: Write `atelier/vite.config.ts` and `atelier/vitest.config.ts`**

```ts
// atelier/vite.config.ts
import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
  server: { port: 5180, strictPort: true },
  build: { outDir: 'dist', sourcemap: true },
});
```

```ts
// atelier/vitest.config.ts
import { defineConfig } from 'vitest/config';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
  test: {
    environment: 'jsdom',
    globals: true,
    setupFiles: ['./tests/setup.ts'],
    include: ['src/**/*.test.ts', 'src/**/*.test.tsx'],
  },
});
```

- [ ] **Step 3: Write `atelier/tsconfig.json`**

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "lib": ["ES2022", "DOM", "DOM.Iterable"],
    "module": "ESNext",
    "moduleResolution": "bundler",
    "jsx": "react-jsx",
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "noImplicitOverride": true,
    "noUnusedLocals": true,
    "noUnusedParameters": true,
    "verbatimModuleSyntax": true,
    "skipLibCheck": true,
    "noEmit": true,
    "isolatedModules": true,
    "resolveJsonModule": true,
    "types": ["vitest/globals"]
  },
  "include": ["src", "tests", "vite.config.ts", "vitest.config.ts", "playwright.config.ts"]
}
```

- [ ] **Step 4: Write `atelier/src/contract/index.ts` (FROZEN — all bots code against this)**

```ts
export type Vec2 = [number, number];
export type Vec3 = [number, number, number];

export type Tone = 'proved' | 'warn' | 'fail' | 'neutral';

export type GeometrySpec =
  | { kind: 'box'; at: Vec3; size: Vec3 }
  | { kind: 'cyl'; from: Vec3; to: Vec3; r0: number; r1?: number }
  | { kind: 'revolve'; profile: Vec2[]; segments: number }
  | { kind: 'loft'; stations: Vec3[] }
  | { kind: 'extrude'; poly: Vec2[]; depth: number }
  | { kind: 'tube'; points: Vec3[]; radius: number };

export interface Part {
  id: string;
  label: string;
  balloon?: number;
  explode?: Vec3;
  sectioned?: boolean;
  geometry: GeometrySpec;
}

export interface IconProps {
  size?: number;
  className?: string;
  tone?: Tone;
  annotated?: boolean;
  title?: string;
}

export interface PlateProps {
  className?: string;
  tone?: Tone;
  title?: string;
}
```

- [ ] **Step 5: Write `atelier/src/contract/tokens.ts` (FROZEN)**

```ts
export const BOARD = {
  page: '#0c0d0e',
  plate: '#141516',
  raised: '#1a1d20',
  line: '#586068',
  rib: '#2e3338',
  edgeHi: '#b2b8be',
  ink: '#8a9096',
  inkHi: '#e8ecee',
  live: '#f4f6f7',
  accent: '#74c7b0',
  warn: '#d9a441',
  fail: '#d4645c',
} as const;

export const SHADE = [
  '#111315',
  '#171a1d',
  '#1e2226',
  '#262b30',
  '#343a40',
  '#454c53',
] as const;

export const STROKE = {
  structure: 1.05,
  cutEdge: 1.35,
  hidden: 0.75,
  centerline: 0.6,
  hatch: 0.5,
  leader: 0.9,
} as const;

export const DASH = {
  hidden: '2.5 2',
  centerline: '8 2 1.6 2',
} as const;

export const DURATION = { d1: 120, d2: 240, d3: 480, d4: 960 } as const;

export const EASE = {
  standard: 'cubic-bezier(0.22, 0.61, 0.36, 1)',
  feature: 'cubic-bezier(0.16, 0.84, 0.44, 1)',
} as const;

export const ISO = { azDeg: 42, elDeg: 30 } as const;
```

- [ ] **Step 6: Write `atelier/src/contract/motion.tsx` (FROZEN — shared by Motion and Stage)**

```tsx
import {
  createContext,
  useContext,
  useEffect,
  useMemo,
  useState,
  type ReactNode,
} from 'react';

interface MotionContextValue {
  reduced: boolean;
}

const MotionContext = createContext<MotionContextValue>({ reduced: false });

export function MotionProvider({ children }: { children: ReactNode }) {
  const [reduced, setReduced] = useState(false);

  useEffect(() => {
    const mq = window.matchMedia('(prefers-reduced-motion: reduce)');
    const apply = () => setReduced(mq.matches);
    apply();
    mq.addEventListener('change', apply);
    return () => mq.removeEventListener('change', apply);
  }, []);

  const value = useMemo(() => ({ reduced }), [reduced]);
  return <MotionContext.Provider value={value}>{children}</MotionContext.Provider>;
}

/** True when the visitor asked for reduced motion. Components must render
 *  the FINAL state immediately when this is true — never an intermediate frame. */
export function useReducedMotion(): boolean {
  return useContext(MotionContext).reduced;
}
```

- [ ] **Step 7: Write `atelier/src/main.tsx`, `atelier/src/App.tsx`, `atelier/index.html`**

```tsx
// atelier/src/main.tsx
import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import { App } from './App';
import { MotionProvider } from './contract/motion';

const host = document.getElementById('root');
if (!host) throw new Error('atelier: #root missing');

createRoot(host).render(
  <StrictMode>
    <MotionProvider>
      <App />
    </MotionProvider>
  </StrictMode>,
);
```

```tsx
// atelier/src/App.tsx
export function App() {
  return (
    <main className="atelier" data-testid="atelier-root">
      <h1>Atelier</h1>
      <p>Scaffold ready.</p>
    </main>
  );
}
```

```html
<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>CONDUIT Atelier</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="/src/main.tsx"></script>
  </body>
</html>
```

- [ ] **Step 8: Write `atelier/tests/setup.ts` and `atelier/playwright.config.ts`**

```ts
// atelier/tests/setup.ts
import '@testing-library/jest-dom/vitest';
```
**Do not add `@testing-library/jest-dom`** — it is not an allowed dependency. Use this instead:

```ts
// atelier/tests/setup.ts
// Intentionally minimal. Tests assert on rendered markup and attributes
// directly, so no DOM matcher library is required.
export {};
```

```ts
// atelier/playwright.config.ts
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './tests',
  testMatch: /.*\.spec\.ts/,
  use: {
    baseURL: 'http://localhost:5180',
    trace: 'on-first-retry',
  },
  webServer: {
    command: 'npm run dev',
    url: 'http://localhost:5180',
    reuseExistingServer: !process.env.CI,
    timeout: 60_000,
  },
  projects: [{ name: 'chromium', use: { ...devices['Desktop Chrome'] } }],
});
```

- [ ] **Step 9: Install and verify the scaffold**

Run: `cd atelier && npm install && npm run typecheck && npm test && npm run build`
Expected: install succeeds, typecheck passes with zero errors, `vitest run` reports "No test files found" as success, `vite build` emits `atelier/dist/`.

- [ ] **Step 10: Commit**

```bash
git add atelier
git commit -m "build(atelier): scaffold isolated React 19 workspace with frozen contract"
```

---

### Task 1: Extend the isometric engine with motorcycle-magazine anatomy (Drafter)

**Files:**
- Create: `atelier/src/illustration/engine/*.ts` (10 files, per the File Structure map)
- Create: `atelier/src/illustration/engine/index.ts`
- Test: `atelier/src/illustration/engine/engine.test.ts`

**Interfaces:**
- Consumes: `GeometrySpec`, `Part`, `Vec2`, `Vec3` from `../../contract`; `BOARD`, `SHADE`, `STROKE`, `DASH`, `ISO` from `../../contract/tokens`.
- Produces (the API every later task depends on):

```ts
// atelier/src/illustration/engine/index.ts
export interface Face {
  /** Projected 2D points in the viewBox coordinate space. */
  points: Vec2[];
  /** Unit normal in view space. */
  normal: Vec3;
  /** Shade ramp index 0..5. */
  shade: number;
  /** True when this face is a cut surface and must be hatched. */
  cut: boolean;
  /** True when the face is back-facing and should be drawn as a hidden edge. */
  hidden: boolean;
}

export interface Edge {
  a: Vec2;
  b: Vec2;
  kind: 'structure' | 'cut' | 'hidden' | 'centerline';
}

export interface Assembly {
  parts: Part[];
  /** Camera azimuth/elevation in degrees. */
  azDeg: number;
  elDeg: number;
  /** Assembly axis used for explode offsets. */
  axis: Vec3;
  /** Explode gap multiplier. */
  explodeScale: number;
  /** Optional parts list rendered beneath the plate. */
  partsList: boolean;
}

export interface RenderedPlate {
  /** viewBox attribute value, e.g. "0 0 640 480". */
  viewBox: string;
  faces: Face[];
  edges: Edge[];
  /** Balloon anchors in viewBox space, one per part that has a balloon. */
  balloons: Array<{ partId: string; number: number; at: Vec2 }>;
  /** Leader polylines from part anchor to balloon anchor. */
  leaders: Array<{ partId: string; points: Vec2[] }>;
  /** Centreline segments. */
  centerlines: Array<{ a: Vec2; b: Vec2 }>;
  /** Dimension lines with terminator ticks and a value label. */
  dimensions: Array<{ a: Vec2; b: Vec2; label: string }>;
  /** Parts-list rows. */
  bill: Array<{ number: number; label: string }>;
}

/** Project an assembly into drawable geometry. Pure — no DOM, no React. */
export function projectAssembly(assembly: Assembly): RenderedPlate;

/** Build the SVG element tree for a projected assembly. */
export function renderPlate(
  plate: RenderedPlate,
  options: { idPrefix: string; tone: Tone; annotated: boolean; title?: string },
): React.ReactElement;

/** Balloon circle radius in viewBox units. */
export const BALLOON_R = 9;
```

- [ ] **Step 1: Write the failing engine test**

Create `atelier/src/illustration/engine/engine.test.ts`:

```ts
import { describe, expect, it } from 'vitest';
import { projectAssembly } from './index';
import type { Assembly } from './index';

const base: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: false,
  parts: [
    { id: 'a', label: 'Rotor', balloon: 1, geometry: { kind: 'box', at: [0, 0, 0], size: [10, 10, 4] } },
    { id: 'b', label: 'Stator', balloon: 2, explode: [0, 0, 12], sectioned: true, geometry: { kind: 'box', at: [0, 0, 20], size: [12, 12, 4] } },
  ],
};

describe('projectAssembly', () => {
  it('separates a part along the assembly axis', () => {
    const plate = projectAssembly(base);
    expect(plate.faces.length).toBeGreaterThan(0);
    expect(plate.balloons).toHaveLength(2);
  });

  it('marks sectioned parts as cut faces', () => {
    const plate = projectAssembly(base);
    expect(plate.faces.some((f) => f.cut)).toBe(true);
  });

  it('emits a leader from every ballooned part', () => {
    const plate = projectAssembly(base);
    expect(plate.leaders).toHaveLength(2);
    for (const l of plate.leaders) expect(l.points.length).toBeGreaterThanOrEqual(2);
  });

  it('is deterministic', () => {
    expect(projectAssembly(base)).toEqual(projectAssembly(base));
  });
});
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd atelier && npx vitest run src/illustration/engine/engine.test.ts`
Expected: FAIL — "Cannot find module './index'".

- [ ] **Step 3: Implement the engine**

Port the projection and geometry code from `v8-iso/iso-cad.mjs` (read it; do not modify it). The
isometric camera in that file computes:

```js
const az = (azDeg * Math.PI) / 180;
const el = (elDeg * Math.PI) / 180;
const V = [Math.cos(el) * Math.cos(az), Math.cos(el) * Math.sin(az), Math.sin(el)];
const Rx = [Math.sin(az), -Math.cos(az), 0];
const Ds = [Math.sin(el) * Math.cos(az), Math.sin(el) * Math.sin(az), -Math.cos(el)];
```

Reuse that basis exactly so atelier plates and the published `v8-iso` plates read as one set.

Implement each module with one responsibility:

- `camera.ts` — `cameraFor(azDeg, elDeg)` returning `{ project(p: Vec3): Vec2, viewNormal(n: Vec3): Vec3 }`.
- `geometry.ts` — `facesFor(spec: GeometrySpec): Array<{ points: Vec3[]; normal: Vec3 }>`. Support all six `GeometrySpec` kinds. For `revolve`/`loft`/`tube`, triangulate like `iso-cad.mjs` does; a coarse faceted result is correct and matches the existing plates.
- `shade.ts` — `shadeFor(normal: Vec3, light: Vec3): number` returning 0..5. The existing `iso-cad.mjs` has `shadeClass(n, opts)`; port its thresholds so shading matches the published plates.
- `hatch.ts` — `hatchPattern(idPrefix: string, index: number)` returning an SVG `<pattern>` descriptor. `index % 2` selects 45° vs 135° so **adjacent parts hatch in opposite directions** (spec 5.3 rule 4). Hatch stroke width `STROKE.hatch`, opacity ~0.5.
- `balloon.ts` — `balloonAnchor(viewBox, from: Vec2): Vec2` placing the balloon outside the drawing bounds on the side with more room; must not overlap the drawing.
- `leader.ts` — `leaderPath(from: Vec2, to: Vec2): Vec2[]` producing a 2- or 3-point polyline (never crossing another leader).
- `dimension.ts` — `dimensionLine(a: Vec2, b: Vec2, label: string)` producing a dimension segment with extension lines and tick terminators.
- `centerline.ts` — `centerlineFor(part)` returning a dash-dot segment along the part's symmetry axis, extended ~3% past the feature.
- `explode.ts` — `explodedOffset(part: Part, assembly: Assembly): Vec3` applying `part.explode` scaled by `assembly.explodeScale` along `assembly.axis`.
- `partsList.ts` — `billFor(parts: Part[])` returning rows sorted by balloon number.
- `render.ts` — `renderPlate` composing `<svg>` with `<defs>` (hatch patterns), `<path>` faces, `<line>`/`<polyline>` edges, balloons, leaders, dimensions, centerlines, and the parts list. Use `useId()`-derived `idPrefix` so `url(#hatch-…)` references never collide across instances.

`projectAssembly` must be pure and deterministic — same input, deep-equal output.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/illustration/engine/engine.test.ts`
Expected: PASS, 4 tests.

- [ ] **Step 5: Typecheck and commit**

Run: `cd atelier && npm run typecheck`
Expected: zero errors.

```bash
git add atelier/src/illustration/engine
git commit -m "feat(atelier): extend isometric engine with hatching, balloons, explode, centerlines, dimensions"
```

---

### Task 2: The eight exploded-isometric icon components (Drafter)

**Files:**
- Create: `atelier/src/illustration/icons/{Isolate,PointerTagging,HiddenClasses,Parser,Ignition,OldSpace,NewSpace,Ratchet}Icon.tsx`
- Create: `atelier/src/illustration/icons/index.ts`
- Test: `atelier/src/illustration/icons/icons.test.tsx`

**Interfaces:**
- Consumes: `projectAssembly`, `renderPlate` from `../engine`; `IconProps` from `../../contract`.
- Produces: eight components plus a barrel exporting all eight.

```ts
// atelier/src/illustration/icons/index.ts
export { IsolateIcon } from './IsolateIcon';
export { PointerTaggingIcon } from './PointerTaggingIcon';
export { HiddenClassesIcon } from './HiddenClassesIcon';
export { ParserIcon } from './ParserIcon';
export { IgnitionIcon } from './IgnitionIcon';
export { OldSpaceIcon } from './OldSpaceIcon';
export { NewSpaceIcon } from './NewSpaceIcon';
export { RatchetIcon } from './RatchetIcon';
```

Each icon component has this exact shape:

```tsx
export function IsolateIcon({ size = 32, className, tone = 'neutral', annotated = true, title }: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(ISOLATE_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title });
}
```

- [ ] **Step 1: Write the failing icon test**

Create `atelier/src/illustration/icons/icons.test.tsx`:

```tsx
import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { IsolateIcon } from './IsolateIcon';
import { RatchetIcon } from './RatchetIcon';

const idsIn = (html: string) =>
  [...html.matchAll(/id="([^"]+)"/g)].map((m) => m[1] ?? '');

describe('icons', () => {
  it('renders an inline svg element', () => {
    const html = renderToStaticMarkup(<IsolateIcon size={48} />);
    expect(html).toContain('<svg');
    expect(html).toContain('viewBox');
  });

  it('honours the size prop', () => {
    const html = renderToStaticMarkup(<IsolateIcon size={64} />);
    expect(html).toMatch(/width="64"/);
  });

  it('namespaces defs ids across sibling instances', () => {
    const html = renderToStaticMarkup(
      <>
        <IsolateIcon />
        <IsolateIcon />
      </>,
    );
    const ids = idsIn(html);
    expect(ids.length).toBeGreaterThan(0);
    expect(new Set(ids).size).toBe(ids.length);
  });

  it('omits balloons when annotated is false', () => {
    const on = renderToStaticMarkup(<IsolateIcon annotated />);
    const off = renderToStaticMarkup(<IsolateIcon annotated={false} />);
    expect(on.length).toBeGreaterThan(off.length);
  });

  it('renders an accessible title when provided', () => {
    const html = renderToStaticMarkup(<RatchetIcon title="The ratchet" />);
    expect(html).toContain('<title');
    expect(html).toContain('The ratchet');
  });
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx vitest run src/illustration/icons/icons.test.tsx`
Expected: FAIL — "Cannot find module './IsolateIcon'".

- [ ] **Step 3: Author the eight assemblies**

Each icon file defines its assembly as a module-level constant and exports the component.

**Subject matter must come from the real repository.** Read the matching `v8-iso/pages/fig-*.html`
to recover the actual geometry, then rebuild it with the engine's primitives:

| Icon | Source to read | Subject |
|---|---|---|
| `IsolateIcon` | `v8-iso/pages/fig-01-isolate.html` | Twin-silo process skid: two silo stacks, a shared base slab, the connecting channel. ~6 parts. |
| `PointerTaggingIcon` | `fig-02-pointer-tagging.html` | Tagged pointer lattice: a lattice of tagged cells with a pointer field. ~7 parts. |
| `HiddenClassesIcon` | `fig-03-hidden-classes.html` | Hidden-class transition tree: map transitions between class shapes. ~7 parts. |
| `ParserIcon` | `fig-04-parser.html` | Lexer → Pratt parser → AST pipeline in three stages. ~6 parts. |
| `IgnitionIcon` | `fig-05-ignition.html` | Bytecode dispatch loop as a closed circuit. ~6 parts. |
| `OldSpaceIcon` | `fig-07-old-space.html` | Old-generation heap: segmented slabs plus the remembered-set barrier. ~7 parts. |
| `NewSpaceIcon` | `fig-08-new-space.html` | Scavenger nursery: semi-space with allocation bump and survivors. ~6 parts. |
| `RatchetIcon` | `browser/ratchet.json` + `scripts/collect_stats.py` | The ratchet: a locked pawl engaging a toothed wheel, with the trusted-item count as the wheel's angle. ~6 parts. |

Rules for every icon:
- 5–8 parts. Fewer reads as a blob; more reads as noise at 32px.
- At least one `sectioned: true` part, so the hatching cue is always present.
- At least one part with a `balloon` number; consecutive numbers 1..n in assembly order.
- `explode` offsets along the shared assembly axis (`[0,0,1]` for vertical stacks,
  `[1,0,0]` for horizontal), with a consistent gap.
- Must remain legible at 24px: silhouette over detail.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/illustration/icons/icons.test.tsx`
Expected: PASS, 5 tests.

- [ ] **Step 5: Typecheck and commit**

Run: `cd atelier && npm run typecheck`
Expected: zero errors.

```bash
git add atelier/src/illustration/icons
git commit -m "feat(atelier): add eight exploded-isometric machinery icons"
```

---

### Task 3: The two large cutaway plates (Drafter)

**Files:**
- Create: `atelier/src/illustration/plates/{V8CorePlate,KernelRendererPlate}.tsx`
- Create: `atelier/src/illustration/plates/index.ts`

**Interfaces:**
- Consumes: `projectAssembly`, `renderPlate` from `../engine`; `PlateProps` from `../../contract`.
- Produces:

```ts
export function V8CorePlate(props: PlateProps): React.ReactElement;
export function KernelRendererPlate(props: PlateProps): React.ReactElement;
```

- [ ] **Step 1: Write the failing plate test**

Create `atelier/src/illustration/plates/plates.test.tsx`:

```tsx
import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { V8CorePlate } from './V8CorePlate';
import { KernelRendererPlate } from './KernelRendererPlate';

describe('plates', () => {
  it('renders the V8 core plate with a parts list', () => {
    const html = renderToStaticMarkup(<V8CorePlate />);
    expect(html).toContain('<svg');
    expect(html.toLowerCase()).toContain('parts');
  });

  it('hatches design-only components on the strategy plate', () => {
    const html = renderToStaticMarkup(<KernelRendererPlate />);
    expect(html).toContain('url(#');
  });
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx vitest run src/illustration/plates/plates.test.tsx`
Expected: FAIL — "Cannot find module './V8CorePlate'".

- [ ] **Step 3: Author the plates**

**`V8CorePlate`** — the eight V8 Mandatory Core machines as ONE continuous exploded assembly
along a shared vertical axis: base slab, isolate, pointer-tagging lattice, hidden-class tree,
parser pipeline, ignition loop, old space, new space. 12–16 parts. `partsList: true`.
Title block: figure number, plate name, scale, part count.

**`KernelRendererPlate`** — the Act 3 strategy plate from `docs/site-redesign-proposal.md`:
the proved kernel in front of disposable per-site renderers, with design-only components
(kernel theorems, Nanvix renderer isolation, HTML/CSS layout) **hatched** so they read as
not-yet-proved. The proved components stay clean. This is the single most important semantic
distinction in the whole set — hatched means "design only".

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/illustration/plates/plates.test.tsx`
Expected: PASS, 2 tests.

- [ ] **Step 5: Typecheck and commit**

```bash
git add atelier/src/illustration/plates
git commit -m "feat(atelier): add V8 core exploded plate and kernel/renderer strategy plate"
```

---

### Task 4: Tier 1 — animated numbers and stats (Motion)

**Files:**
- Create: `atelier/src/viz/stats/{CountFigure,OdometerReels,StatTile,SplitBar,RadialGauge,DeltaChip}.tsx`
- Create: `atelier/src/viz/stats/index.ts`

**Interfaces:**
- Consumes: `useReducedMotion` from `../../contract/motion`; `DURATION`, `EASE` from `../../contract/tokens`.
- Produces:

```ts
export function CountFigure(props: {
  value: number;
  label?: string;
  suffix?: string;
  duration?: number;
  className?: string;
}): React.ReactElement;

export function OdometerReels(props: {
  value: number;
  digits?: number;
  className?: string;
}): React.ReactElement;

export function StatTile(props: {
  value: string;
  label: string;
  hint?: string;
  tone?: Tone;
  className?: string;
}): React.ReactElement;

export function SplitBar(props: {
  segments: Array<{ id: string; label: string; value: number; tone?: Tone }>;
  className?: string;
}): React.ReactElement;

export function RadialGauge(props: {
  value: number;
  max: number;
  label?: string;
  className?: string;
}): React.ReactElement;

export function DeltaChip(props: {
  delta: number;
  unit?: string;
  className?: string;
}): React.ReactElement;
```

- [ ] **Step 1: Write the failing stats test**

Create `atelier/src/viz/stats/stats.test.tsx`:

```tsx
import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { CountFigure } from './CountFigure';
import { DeltaChip } from './DeltaChip';
import { RadialGauge } from './RadialGauge';

describe('stats', () => {
  it('renders the target value in markup', () => {
    const html = renderToStaticMarkup(<CountFigure value={12480} />);
    expect(html).toContain('12,480');
  });

  it('renders a negative delta with its sign', () => {
    const html = renderToStaticMarkup(<DeltaChip delta={-44} unit="%" />);
    expect(html).toContain('-44%');
  });

  it('renders the gauge arc for the given ratio', () => {
    const html = renderToStaticMarkup(<RadialGauge value={38} max={100} />);
    expect(html).toContain('<svg');
  });
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx vitest run src/viz/stats/stats.test.tsx`
Expected: FAIL — "Cannot find module './CountFigure'".

- [ ] **Step 3: Implement the six components**

Remocn's `numbers` catalog is the choreography benchmark — read
https://remocn.dev/docs/numbers for the bar. Differences from Remocn, all mandatory:
use this repo's palette from `contract/tokens`; use JetBrains Mono; no drop shadows; no bounce.

Implementation rules:
- Count-up via `requestAnimationFrame` with an eased ramp over `DURATION.d3` (480ms). When
  `useReducedMotion()` is true, render the final value immediately with **no** animation frames.
- `OdometerReels` renders one reel per digit; each reel is a vertical strip of 0–9 translated
  by `translateY`. During a roll, all reels start together and stop together — no per-digit stagger.
- `StatTile` reveals in the order value → label → hint, `DURATION.d1` apart.
- `SplitBar` segments animate width from 0, staggered `DURATION.d1` apart, then the total lands.
- `RadialGauge` sweeps the arc with `stroke-dasharray`/`stroke-dashoffset`.
- `DeltaChip` colours by sign: positive → `BOARD.accent`, negative → `BOARD.fail`. Zero → `BOARD.ink`.
- All components accept `className` and merge it onto the root element.
- Every animated value must settle on the exact final value — never a rounded approximation.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/viz/stats/stats.test.tsx`
Expected: PASS, 3 tests.

- [ ] **Step 5: Typecheck and commit**

```bash
git add atelier/src/viz/stats
git commit -m "feat(atelier): add tier-1 animated stats components"
```

---

### Task 5: The RatchetCounter — the signature component (Motion)

**Files:**
- Create: `atelier/src/viz/stats/RatchetCounter.tsx`
- Modify: `atelier/src/viz/stats/index.ts` (add the export)

**Interfaces:**
- Consumes: `useReducedMotion` from `../../contract/motion`; `BOARD` from `../../contract/tokens`.
- Produces:

```ts
export function RatchetCounter(props: {
  /** The trusted-item count. The ratchet only ever goes down. */
  trusted: number;
  /** Optional previous-release count, for the "since last release" delta. */
  previous?: number;
  label?: string;
  className?: string;
}): React.ReactElement;
```

- [ ] **Step 1: Write the failing test**

Create `atelier/src/viz/stats/ratchet.test.tsx`:

```tsx
import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { RatchetCounter } from './RatchetCounter';

describe('RatchetCounter', () => {
  it('renders the trusted count', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={0} />);
    expect(html).toContain('0');
  });

  it('shows a violation state when the count rises above the previous release', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={12} previous={4} />);
    expect(html).toContain('data-violation="true"');
  });

  it('shows no violation when the count holds or falls', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={4} previous={4} />);
    expect(html).toContain('data-violation="false"');
  });
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx vitest run src/viz/stats/ratchet.test.tsx`
Expected: FAIL — "Cannot find module './RatchetCounter'".

- [ ] **Step 3: Implement RatchetCounter**

The ratchet's whole meaning is that the number never rises between releases. So:

- When `trusted < previous`: the counter **animates downward** and settles on `trusted`, tone `BOARD.accent`.
- When `trusted === previous`: holds, no animation.
- When `trusted > previous`: **must not animate upward**. Set `data-violation="true"` on the root,
  render the value in `BOARD.fail`, and hold it static with a visible violation mark. This is the
  behaviour that makes the component honest — an upward animation would be a lie about the
  invariant it represents.
- With `useReducedMotion()` true, render the final state with no animation in every branch.
- The root element carries `data-trusted={trusted}`, `data-previous={previous ?? ''}` and
  `data-violation` so tests and Playwright can assert on it.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/viz/stats/ratchet.test.tsx`
Expected: PASS, 3 tests.

- [ ] **Step 5: Typecheck and commit**

```bash
git add atelier/src/viz/stats
git commit -m "feat(atelier): add RatchetCounter that only ever animates downward"
```

---

### Task 6: Tier 2 — the interactive tri-color GC heap scene (Stage)

**Files:**
- Create: `atelier/src/viz/stage/threeScene.ts`
- Create: `atelier/src/viz/stage/GcHeapScene.tsx`
- Create: `atelier/src/viz/stage/index.ts`

**Interfaces:**
- Consumes: `useReducedMotion` from `../../contract/motion`; `BOARD` from `../../contract/tokens`.
- Produces:

```ts
export function GcHeapScene(props: {
  /** Objects in the heap. `color` is the tri-color mark. */
  objects: Array<{ id: string; position: [number, number, number]; color: 'white' | 'grey' | 'black' }>;
  /** Pointers between objects. */
  edges: Array<{ from: string; to: string }>;
  /** Highlight a tri-color barrier violation. */
  violation?: { from: string; to: string } | null;
  className?: string;
}): React.ReactElement;
```

- [ ] **Step 1: Write the failing scene test**

Create `atelier/src/viz/stage/scene.test.tsx`:

```tsx
import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { GcHeapScene } from './GcHeapScene';

describe('GcHeapScene', () => {
  it('renders a canvas host element', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={[{ id: 'a', position: [0, 0, 0], color: 'white' }]} edges={[]} />,
    );
    expect(html).toContain('canvas');
  });

  it('marks a tri-color violation', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene
        objects={[
          { id: 'a', position: [0, 0, 0], color: 'grey' },
          { id: 'b', position: [1, 0, 0], color: 'black' },
        ]}
        edges={[{ from: 'a', to: 'b' }]}
        violation={{ from: 'a', to: 'b' }}
      />,
    );
    expect(html).toContain('data-violation="true"');
  });
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx vitest run src/viz/stage/scene.test.tsx`
Expected: FAIL — "Cannot find module './GcHeapScene'".

- [ ] **Step 3: Implement the scene**

- `threeScene.ts` — a plain-`three` wrapper class: `createGcHeapScene(canvas, opts)` returning
  `{ update(objects, edges, violation), dispose(), resize() }`. Use `OrbitControls` from
  `three/examples/jsm/controls/OrbitControls.js` (ships with `three`; no new dependency).
  Render objects as small boxes coloured by tri-color mark: white `BOARD.live`, grey `BOARD.ink`,
  black `BOARD.board-raised`. Edges as thin lines. A violation edge draws in `BOARD.fail`.
  Call `renderer.setAnimationLoop` and **always** `renderer.dispose()` and remove listeners on unmount.
- `GcHeapScene.tsx` — React wrapper: `useRef` for the canvas, `useEffect` to create the scene and
  `useEffect` to update it when props change. The wrapper renders a `<canvas>` inside a
  `<div data-testid="gc-heap-scene">`, and carries `data-violation` on the root.
- The canvas must be created client-side only — guard against SSR (`typeof window === 'undefined'`).
- `useReducedMotion()` true → render a single static frame, no animation loop.
- 60fps target: keep object count modest (the scene is designed for 10–40 objects).

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/viz/stage/scene.test.tsx`
Expected: PASS, 2 tests.

- [ ] **Step 5: Typecheck and commit**

```bash
git add atelier/src/viz/stage
git commit -m "feat(atelier): add interactive tri-color GC heap WebGL scene"
```

---

### Task 7: Tier 3 — two step-through algorithm scenes (Stage)

**Files:**
- Create: `atelier/src/viz/stage/stepper.ts`
- Create: `atelier/src/viz/stage/PrattParserScene.tsx`
- Create: `atelier/src/viz/stage/TriColorGcScene.tsx`
- Modify: `atelier/src/viz/stage/index.ts` (add exports)

**Interfaces:**
- Consumes: `useReducedMotion` from `../../contract/motion`; `DURATION`, `EASE`, `BOARD` from `../../contract/tokens`.
- Produces:

```ts
// atelier/src/viz/stage/stepper.ts
export interface Step {
  /** Caption explaining what this step demonstrates. */
  caption: string;
  /** The spec clause or invariant this step corresponds to, e.g. "ECMA-262 §11.8.6". */
  clause?: string;
  /** Per-step rendered content. */
  render: (t: number) => React.ReactNode;
}

export interface StepperProps {
  steps: Step[];
  className?: string;
  /** Label for the transport controls, for screen readers. */
  label?: string;
}

export function Stepper(props: StepperProps): React.ReactElement;
```

`Stepper` provides: play, pause, step-forward, step-back, reset, a scrubbable range input, a
step counter, and a caption area. It must be keyboard operable (arrow keys move between steps)
and must expose `data-step-index` and `data-step-count` on the root for Playwright.

- [ ] **Step 1: Write the failing stepper test**

Create `atelier/src/viz/stage/stepper.test.tsx`:

```tsx
import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { Stepper } from './stepper';

const steps = [
  { caption: 'Start', render: () => <span>A</span> },
  { caption: 'Next', render: () => <span>B</span> },
];

describe('Stepper', () => {
  it('exposes step position for tests', () => {
    const html = renderToStaticMarkup(<Stepper steps={steps} />);
    expect(html).toContain('data-step-index="0"');
    expect(html).toContain('data-step-count="2"');
  });

  it('renders the first step caption', () => {
    const html = renderToStaticMarkup(<Stepper steps={steps} />);
    expect(html).toContain('Start');
  });
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx vitest run src/viz/stage/stepper.test.tsx`
Expected: FAIL — "Cannot find module './stepper'".

- [ ] **Step 3: Implement the stepper and the two scenes**

`stepper.ts` — transport controls as real `<button>`s with `aria-label`s, a range input for
scrubbing, `data-step-index` / `data-step-count` on the root. Use `useReducedMotion()` to skip
the transition animation between steps.

**`PrattParserScene`** — traces `vjs_syntax` (crate J3). Steps must correspond to the real
pipeline: token stream → binding powers → precedence climbing → AST. Read
`browser/vjs-syntax/` to get the real clause names. Each step names its ECMA-262 clause in
`clause`.

**`TriColorGcScene`** — traces `vjs_gc` (crate J6). Steps: root set → mark phase (grey→black) →
scan → sweep. Annotate the tri-color invariant: *a grey object must have no black pointers*.
Name the real invariant in `clause`.

Both scenes render as SVG (not WebGL) — they are 2D algorithm diagrams, matching the manim-dsa
reference. Use the drafter grammar: hairline strokes, mono labels, no fills as shadow.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cd atelier && npx vitest run src/viz/stage/stepper.test.tsx`
Expected: PASS, 2 tests.

- [ ] **Step 5: Typecheck and commit**

```bash
git add atelier/src/viz/stage
git commit -m "feat(atelier): add Pratt parser and tri-color GC step-through scenes"
```

---

### Task 8: Gallery, accessibility, and the test suites (Proof)

**Files:**
- Create: `atelier/src/gallery/{Gallery,GalleryNav,IconSheet,PlateSheet,StatsSheet,SceneSheet}.tsx`
- Create: `atelier/src/gallery/gallery.css`
- Create: `atelier/tests/{illustration,stats,scene}.test.tsx`
- Create: `atelier/tests/{atelier,reduced-motion}.spec.ts`
- Modify: `atelier/src/App.tsx` (mount the gallery) — **Proof owns `App.tsx` edits only**;
  Chief owns the scaffold itself.

**Interfaces:**
- Consumes: every icon, plate and component from Tasks 2–7; `BOARD` tokens.
- Produces: a gallery app that renders every piece on the dark drafter board.

- [ ] **Step 1: Write the failing gallery test**

Create `atelier/tests/atelier.spec.ts`:

```ts
import { expect, test } from '@playwright/test';

test('gallery lists every icon', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('icon-sheet')).toBeVisible();
  await expect(page.getByTestId('icon-isolate')).toBeVisible();
  await expect(page.getByTestId('icon-ratchet')).toBeVisible();
});

test('no console errors on load', async ({ page }) => {
  const errors: string[] = [];
  page.on('console', (m) => m.type() === 'error' && errors.push(m.text()));
  await page.goto('/');
  await page.waitForTimeout(500);
  expect(errors).toEqual([]);
});
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cd atelier && npx playwright test tests/atelier.spec.ts`
Expected: FAIL — `icon-sheet` not found.

- [ ] **Step 3: Build the gallery**

`App.tsx` renders `<Gallery />`. `Gallery` is a tabbed shell over `IconSheet`, `PlateSheet`,
`StatsSheet`, `SceneSheet`, each rendering its items with `data-testid` attributes
(`icon-sheet`, `icon-isolate`, `icon-ratchet`, `plate-sheet`, `stats-sheet`, `scene-sheet`).

`gallery.css` defines the drafter board: page ground `BOARD.page`, panels `BOARD.plate`,
hairline borders in `BOARD.rib`, JetBrains Mono for all text, uppercase tracking on labels.

The Stats sheet must load **real** data. Read `browser/ratchet.json` and `data/stats.json` at
build time via a small loader module in `atelier/src/gallery/data.ts` that imports the JSON
directly (Vite supports JSON imports) and falls back to `{ recorded: false }` when a field is
missing — rendering `not recorded`, never a placeholder number.

- [ ] **Step 4: Write the accessibility, reduced-motion and unit suites**

`atelier/tests/illustration.test.tsx` — asserts all eight icons render inline SVG, that
`useId` namespaces defs ids across siblings, and that balloons appear only when `annotated`.

`atelier/tests/stats.test.tsx` — asserts the real ratchet data renders, and that a missing
field renders `not recorded`.

`atelier/tests/scene.test.tsx` — asserts both scenes expose `data-step-index` / `data-step-count`
and that the Stepper's controls are keyboard reachable.

`atelier/tests/reduced-motion.spec.ts`:

```ts
import { expect, test } from '@playwright/test';

test.use({ reducedMotion: 'reduce' });

test('reduced motion renders the final counter value immediately', async ({ page }) => {
  await page.goto('/');
  const counter = page.getByTestId('ratchet-counter');
  await expect(counter).toBeVisible();
  await expect(counter).toHaveAttribute('data-settled', 'true');
});
```

- [ ] **Step 5: Run all suites**

Run: `cd atelier && npm test && npm run typecheck && npx playwright test`
Expected: all vitest tests pass, typecheck clean, all Playwright specs pass.

- [ ] **Step 6: Commit**

```bash
git add atelier/src/gallery atelier/tests atelier/src/App.tsx
git commit -m "feat(atelier): add gallery shell, accessibility and test suites"
```

---

### Task 9: Integration and Definition-of-Done verification (Chief)

**Files:**
- Modify: `atelier/src/App.tsx` only if integration requires it.

- [ ] **Step 1: Install, typecheck, build, test**

Run:
```bash
cd atelier && npm install && npm run typecheck && npm run build && npm test && npx playwright test
```
Expected: every step passes with zero errors.

- [ ] **Step 2: Verify the containment constraint**

Run:
```bash
cd /Users/mac/conduit-lab && git diff --stat -- site/ v8-iso/ inkwork/ browser/ data/ scripts/
```
Expected: **empty output.** Nothing outside `atelier/` changed. If this is not empty, revert the
offending change immediately and report it.

- [ ] **Step 3: Verify the full Definition of Done**

Check each of the 10 items in spec section 10 and record pass/fail with evidence:

1. `atelier/` installs, builds, typechecks strict, tests pass → paste command output.
2. 8 icons + 2 plates render with balloons, leaders, hatching → count them in the gallery.
3. Tier 1: 6 components + `RatchetCounter` on real `ratchet.json` / `stats.json` data.
4. Tier 2: one interactive WebGL GC heap scene.
5. Tier 3: two step-through algorithm scenes.
6. Gallery renders every piece, responsive, dark drafter board.
7. `prefers-reduced-motion` path verified by Playwright.
8. Accessible names verified; zero console errors; zero React key/hydration warnings.
9. `site/` byte-identical — from step 2.
10. `docs/drawing-standard.md` written and signed off.

- [ ] **Step 4: Write `docs/drawing-standard.md`**

The normative drawing standard, distilled from spec section 5, as a short document a future
contributor can follow: palette table, stroke table, the nine motorcycle-magazine anatomy rules,
the projection convention, and one annotated worked example. Chief signs it off.

- [ ] **Step 5: Commit and report**

```bash
git add docs/drawing-standard.md atelier
git commit -m "docs(atelier): add drawing standard and integrate the drafting room"
```

Report to the requester: every Definition-of-Done item with its evidence, the list of components
and icons produced, the test/build output, and anything left unfinished or unverified. Do not
claim a check passed without showing the command that proves it.

---

## Self-Review

**Spec coverage** — every spec section maps to a task:

| Spec section | Task |
|---|---|
| 4 Architecture / 4.1 frozen contract | Task 0 |
| 5 Drawing Standard | Task 1 (engine), Tasks 2–3 (application), Task 9 (doc) |
| 6.1 Icons | Task 2 |
| 6.2 Illustrations | Task 3 |
| 6.3 Tier 1 | Task 4 |
| 6.3 `RatchetCounter` | Task 5 |
| 6.4 Tier 2 | Task 6 |
| 6.5 Tier 3 | Task 7 |
| 7 Motion grammar | Task 0 (tokens + `useReducedMotion`), Tasks 4–7 |
| 8 Quality bar | Task 8 (suites), Task 9 (DoD verification) |
| 9 Team structure | Task 0 (Chief), Tasks 1–8 (members), Task 9 (integration) |
| 10 Definition of done | Task 9 Step 3 |
| 11 Risks | Global Constraints + Task 0 (disjoint ownership) |

**Placeholder scan** — no TBD/TODO. Every step names exact files, exact commands, expected
output, and concrete code. Step 8 of Task 0 shows the corrected `setup.ts` after showing the
rejected dependency, so no worker copies the bad version.

**Type consistency** — `GeometrySpec`, `Part`, `IconProps`, `PlateProps`, `Tone` are defined once
in `contract/index.ts` and imported everywhere else. `Assembly`, `RenderedPlate`,
`projectAssembly`, `renderPlate`, `BALLOON_R` are defined once in `engine/index.ts` and used by
Tasks 2, 3. `Step`/`StepperProps`/`Stepper` defined once in `stage/stepper.ts`, used by Task 7 and
Task 8. `useReducedMotion` defined once in `contract/motion.tsx`, used by Tasks 4–7.

**Known deviation, disclosed:** spec section 9 assigns `contract/**` to Chief; MCode writes the
initial frozen version during Task 0 as a pre-dispatch scaffold so no two workers contend for a
shared file. Chief remains the owner and may amend it with MCode's approval.
