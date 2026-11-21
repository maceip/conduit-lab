import * as k from "../kit/iso-kit.mjs";
import { createBench } from "./bench.mjs";

const WIDTH = 620;
const HEIGHT = 390;

const PLATE = { x: -136, y: -68, w: 272, d: 136, r: 8 };
const PLATE_H = 12;
const FOOT_H = 5;

const PROBE_X = 4;
const PROBE_Y = -6;

// Real V8 front-end specimens: Lazy PreParser vs Eager Parser AST zone allocation
const SPECIMENS = [
  {
    id: "lazy-fn",
    name: "fn add(a,b){return a+b}",
    mode: "PreParser (lazy)",
    tokens: 13,
    skipped: 6,
    astNodes: 2,
    height: 6,
  },
  {
    id: "arrow-expr",
    name: "const f = x => x*2 + 1",
    mode: "PreParser + outer decl",
    tokens: 11,
    skipped: 5,
    astNodes: 5,
    height: 10,
  },
  {
    id: "nested-scope",
    name: "function outer(){function inner(){}}",
    mode: "Scope-only skip",
    tokens: 15,
    skipped: 9,
    astNodes: 8,
    height: 14,
  },
  {
    id: "eager-ast",
    name: "function hot(o){return o.x + o.y}",
    mode: "Eager Parser (AST)",
    tokens: 14,
    skipped: 0,
    astNodes: 12,
    height: 18,
  },
];

const CARRIAGE_Z = 3;
const CARRIAGE_TOP = 8;
const BLOCK_W = 10;
const BLOCK_STEP = 12;
const FIRST_BLOCK_LOCAL_X = -23;

// Stops place each specimen block squarely under PROBE_X
const STOPS = SPECIMENS.map(
  (_, idx) => PROBE_X - (FIRST_BLOCK_LOCAL_X + BLOCK_STEP * idx + BLOCK_W / 2),
);
const REACH = [Math.min(...STOPS) - 3, Math.max(...STOPS) + 3];

const P = k.fitProjection(
  [
    ...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0),
    [-124, -26, 44],
    [-26, -36, 72],
    [118, 30, 82],
  ],
  WIDTH,
  HEIGHT,
  { pad: 28, azimuth: 43, elevation: 30 },
);

const B = createBench(P);
const { at, Ln, Dots, slab, cyl, benchPlate, rulerStrip, labelPlate, knurledKnob, dialGauge, cable } = B;

// 1. Surface plate, feet, ruler & single engraved nameplate
benchPlate(PLATE, PLATE_H, FOOT_H);
rulerStrip("stand.ruler", { x: -124, y: 50, w: 172, d: 7, r: 1 }, 0, 0.6);
labelPlate("stand.label", { x: 58, y: 49, w: 66, d: 9, r: 1.2 }, 0, 0.8, { text: "V8 SCAN · AST" });

// 2. Left UTF-16 Source Spool & Feed Roller
slab("feed.base", { x: -126, y: -32, w: 42, d: 46, r: 3 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8 });
slab("feed.plinth", { x: -123, y: -29, w: 36, d: 40, r: 2.5 }, 10, 6, { tone: "mid" }, { steps: 5, bevel: 0.6 });
cyl("feed.flangeBot", -105, -9, 12.5, 16, 2, { tone: "lo" }, { steps: 40 });
cyl("feed.core", -105, -9, 6.5, 18, 11, { tone: "mid" }, { steps: 32, seamZs: [23.5] });
cyl("feed.flangeTop", -105, -9, 12.5, 29, 2.2, { tone: "hi", crease: "lo" }, {
  steps: 44,
  bevel: 0.5,
  extra: Ln(k.ring(-105, -9, 9.2, 31.2, P, 32), { tone: "faint" }),
});
cyl("feed.spindle", -105, -9, 2.8, 31.2, 4.8, { tone: "mid" }, { steps: 20 });
knurledKnob("feed.tension", -105, -9, 4.6, 36, 3.6, { count: 24, pointerAngle: 0.6 });

// Guide roller beside rail entry (clear of rail.stop0 at x = -77..-72, y = -24..17)
cyl("roller.foot", -81, -34, 4.8, 0, 4, { tone: "lo" }, { steps: 24 });
cyl("roller.drum", -81, -34, 3.4, 4, 15, { tone: "mid" }, { steps: 24, seamZs: [8, 15] });
cyl("roller.cap", -81, -34, 4.2, 19, 2, { tone: "hi" }, { steps: 24 });

// Lazy / Eager mode selector turret at front-left
slab("mode.pedestal", { x: -124, y: 20, w: 28, d: 22, r: 2.5 }, 0, 8, { tone: "mid" }, {
  steps: 4,
  bevel: 0.6,
  extra: Ln(k.planOutline(k.insetPlan({ x: -124, y: 20, w: 28, d: 22, r: 2.5 }, 2.5), 8, P, 4), { tone: "faint" }),
});
knurledKnob("mode.knob", -110, 31, 6.5, 8, 4.5, { count: 32, pointerAngle: -0.4 });

// 3. Twin Ground Token Rails & End Stops
for (const [idx, ry] of [[-21, 9].entries()]) {
  // dummy guard not used
}
[-21, 9].forEach((ry, idx) => {
  slab(`rail.bar${idx}`, { x: -72, y: ry, w: 124, d: 5, r: 1 }, 0, 3, { tone: "mid" }, {
    steps: 3,
    bevel: 0.4,
    extra: Dots([-64, -20, 20, 44].map((rx) => at([rx, ry + 2.5, 3])), { size: 0.4 }),
  });
});
for (const [idx, sx] of [[-77, 52].entries()]) {
  // iterate cleanly
}
[-77, 52].forEach((sx, idx) => {
  slab(`rail.stop${idx}`, { x: sx, y: -24, w: 5, d: 41, r: 1.2 }, 0, 7, { tone: "mid" }, {
    steps: 3,
    bevel: 0.5,
    extra: Dots([at([sx + 2.5, -19, 7]), at([sx + 2.5, 12, 7])], { size: 0.45 }),
  });
});
[-42, -2].forEach((tx, idx) => {
  slab(`rail.tie${idx}`, { x: tx, y: -16, w: 6, d: 25, r: 0.8 }, 0, 1.5, { tone: "lo", crease: "none" }, { steps: 2, bevel: 0 });
});

// 4. Scanner Optical Bridge (spans cleanly over rails without touching carriage)
slab("bridge.backFoot", { x: -41, y: -39, w: 16, d: 14, r: 2 }, 0, 4, { tone: "lo" }, { steps: 3, bevel: 0.4 });
slab("bridge.backPost", { x: -39, y: -37, w: 12, d: 10, r: 1.8 }, 4, 42, { tone: "mid" }, { steps: 3, bevel: 0.5, seamZ: 25 });

slab("bridge.frontFoot", { x: -41, y: 17, w: 16, d: 14, r: 2 }, 0, 4, { tone: "lo" }, { steps: 3, bevel: 0.4 });
slab("bridge.frontPost", { x: -39, y: 19, w: 12, d: 10, r: 1.8 }, 4, 42, { tone: "mid" }, { steps: 3, bevel: 0.5, seamZ: 25 });

slab("bridge.beam", { x: -41, y: -38, w: 16, d: 68, r: 2.5 }, 46, 7, { tone: "mid" }, {
  steps: 4,
  bevel: 0.7,
  extra: Dots(
    [
      at([-33, -33, 53]),
      at([-33, 25, 53]),
    ],
    { size: 0.48 },
  ),
});
cyl("scanner.barrelLow", -33, -6, 4.4, 37, 9, { tone: "mid" }, { steps: 28, seamZs: [40] });
cyl("scanner.housing", -33, -6, 7.2, 53, 7, { tone: "hi", crease: "lo" }, { steps: 36, bevel: 0.5 });
cyl("scanner.focus", -33, -6, 5.8, 60, 4.5, { tone: "mid" }, { steps: 32, knurlCount: 30 });
cyl("scanner.lensCap", -33, -6, 4.0, 64.5, 2, { tone: "hi" }, {
  steps: 24,
  extra: Ln(k.ring(-33, -6, 2.4, 66.5, P, 20), { tone: "lo" }),
});

// 5. Moving Token Specimen Carriage (built at startX = STOPS[3])
const REST_IDX = 3;
const startX = STOPS[REST_IDX];
const carPlan = { x: startX - 26, y: -20, w: 52, d: 33, r: 2.5 };
slab("carriage.bed", carPlan, CARRIAGE_Z, CARRIAGE_TOP - CARRIAGE_Z, { tone: "mid" }, {
  steps: 4,
  bevel: 0.6,
  attrs: 'data-part="carriage"',
  extra:
    Dots([-22, -8, 6, 20].map((dx) => at([startX + dx, carPlan.y + carPlan.d - 2.4, CARRIAGE_TOP])), {
      size: 0.4,
      tone: "lo",
    }) +
    Ln(k.lineOnTop([carPlan.x, -16], [carPlan.x + carPlan.w, -16], CARRIAGE_TOP, P), { tone: "faint" }) +
    Ln(k.lineOnTop([carPlan.x, 8.5], [carPlan.x + carPlan.w, 8.5], CARRIAGE_TOP, P), { tone: "faint" }),
});

SPECIMENS.forEach((spec, idx) => {
  const bx = startX + FIRST_BLOCK_LOCAL_X + BLOCK_STEP * idx;
  const bPlan = { x: bx, y: -14, w: BLOCK_W, d: 16, r: 1.1 };
  const isEager = idx === 3;
  slab(`carriage.block${idx}`, bPlan, CARRIAGE_TOP, spec.height, { tone: "hi", crease: "lo", lit: isEager }, {
    steps: 3,
    bevel: 0.45,
    attrs: `data-part="carriage" data-block="${idx}"`,
    extra: Ln(k.planOutline(k.insetPlan(bPlan, 1.8), CARRIAGE_TOP + spec.height, P, 3), { tone: "faint" }),
  });
});

// 6. Right AST Zone Arbour Column, Arm, Plunger & Dial Indicator
slab("ast.base", { x: 60, y: -38, w: 62, d: 70, r: 4 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5 });
slab("ast.deck", { x: 64, y: -34, w: 54, d: 62, r: 3 }, 10, 6, { tone: "mid" }, {
  steps: 5,
  bevel: 0.6,
  extra: Ln(k.planOutline(k.insetPlan({ x: 64, y: -34, w: 54, d: 62, r: 3 }, 3), 16, P, 4), { tone: "faint" }),
});

// AST Zone stacked arena trays on the right deck
for (let layer = 0; layer < 3; layer++) {
  const z0 = 16 + layer * 5.2;
  const trayPlan = { x: 70, y: 2, w: 26, d: 20, r: 1.5 };
  slab(`ast.zone${layer}`, trayPlan, z0, 5.2, { tone: layer === 2 ? "hi" : "mid" }, {
    steps: 3,
    bevel: 0.4,
    extra:
      layer === 2
        ? Dots([at([74, 6, z0 + 5.2]), at([92, 6, z0 + 5.2]), at([74, 18, z0 + 5.2]), at([92, 18, z0 + 5.2])], { size: 0.42 })
        : "",
  });
}
knurledKnob("ast.diverterKnob", 104, 12, 5.8, 16, 4.5, { count: 28, pointerAngle: 1.1 });

// Column & overhanging arm carrying AST Dial Gauge at PROBE_X
const POST_X = 100;
const POST_Y = PROBE_Y;
cyl("ast.collar", POST_X, POST_Y, 6.2, 16, 4, { tone: "lo" }, { steps: 28 });
cyl("ast.post", POST_X, POST_Y, 3.8, 20, 34, { tone: "mid", crease: "none" }, { steps: 28, seamZs: [32, 44] });
slab("ast.clamp", { x: POST_X - 8, y: POST_Y - 8, w: 16, d: 16, r: 2.5 }, 54, 8, { tone: "mid" }, { steps: 4, bevel: 0.6 });

const ARM = { x: PROBE_X - 10, y: POST_Y - 5, w: POST_X - PROBE_X + 18, d: 10, r: 2 };
slab("ast.arm", ARM, 62, 5, { tone: "mid" }, {
  steps: 4,
  bevel: 0.5,
  extra: Dots([at([ARM.x + 4, POST_Y, 67]), at([POST_X - 10, POST_Y, 67])], { size: 0.45 }),
});
cyl("ast.postCap", POST_X, POST_Y, 4.6, 67, 3, { tone: "hi" }, { steps: 28, bevel: 0.4 });

// Stationary guide gland under arm + moving plunger resting on specimen block
cyl("probe.gland", PROBE_X, PROBE_Y, 3.6, 49, 13, { tone: "mid" }, { steps: 24, seamZs: [54] });
const restTop = CARRIAGE_TOP + SPECIMENS[REST_IDX].height; // 26
cyl("probe.shoe", PROBE_X, PROBE_Y, 2.8, restTop, 2.4, { tone: "hi", lit: true }, {
  steps: 22,
  attrs: 'data-part="plunger"',
});
cyl("probe.stem", PROBE_X, PROBE_Y, 1.5, restTop + 2.4, 49 - (restTop + 2.4), { tone: "hi", crease: "none", lit: true }, {
  steps: 18,
  attrs: 'data-part="plunger"',
});

// Dial indicator mounted flush on arm at PROBE_X
const DIAL_R = 18;
const { needleAt } = dialGauge("ast.dial", PROBE_X, PROBE_Y, DIAL_R, 67, 9.5, {
  count: 48,
  every: 4,
  needlePart: "needle",
  startTurn: SPECIMENS[REST_IDX].astNodes / 16,
});

// 7. Harness cable from bridge front foot right face (x = -25) to AST base left face (x = 60) in horizontal plane
cable(
  "scan.harness",
  [
    [-25, 24, 2],
    [-2, 24, 2],
    [18, 34, 2],
    [40, 24, 2],
    [60, 24, 2],
  ],
  0.58,
  { tone: "mid", bend: 5 },
);

const svg = B.assembleSvg({
  width: WIDTH,
  height: HEIGHT,
  label:
    "Isometric V8 Scanner and Parser benchtop diverter. A UTF-16 source reel feeds a four-specimen token carriage under an optical scanner bridge and an AST zone dial indicator. Lazy PreParser specimens keep low profile shells while eager parsing raises full AST blocks, lifting the lit probe plunger and turning the AST zone dial.",
});

const liveScript = `
const P = ${JSON.stringify(P)};
const SPECIMENS = ${JSON.stringify(SPECIMENS)};
const STOPS = ${JSON.stringify(STOPS)};
const REACH = ${JSON.stringify(REACH)};
const START_X = ${startX};
const REST_TOP = ${restTop};
const CARRIAGE_TOP = ${CARRIAGE_TOP};
const PROBE_X = ${PROBE_X};
const FIRST_LOCAL = ${FIRST_BLOCK_LOCAL_X};
const BLOCK_STEP = ${BLOCK_STEP};
const BLOCK_W = ${BLOCK_W};
const TIP_R = 2.8;
const DIAL_R = ${DIAL_R};

const stage = document.querySelector(".iso-stage");
const svg = stage.querySelector("svg");
const carriageParts = [...svg.querySelectorAll('[data-part="carriage"]')];
const plungerParts = [...svg.querySelectorAll('[data-part="plunger"]')];
const needle = svg.querySelector('[data-part="needle"]');
const readout = document.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");

const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
const needleAt = (turn) => {
  const a = turn * Math.PI * 2;
  return lineOnTop(
    [${PROBE_X} - Math.sin(a) * 3.0, ${PROBE_Y} + Math.cos(a) * 3.0],
    [${PROBE_X} + Math.sin(a) * (${DIAL_R} - 3.8), ${PROBE_Y} - Math.cos(a) * (${DIAL_R} - 3.8)],
    ${67 + 9.5 + 0.2},
    P
  );
};

function heightUnder(cx) {
  let top = CARRIAGE_TOP;
  SPECIMENS.forEach((s, i) => {
    const from = cx + FIRST_LOCAL + BLOCK_STEP * i;
    const to = from + BLOCK_W;
    if (to > PROBE_X - TIP_R && from < PROBE_X + TIP_R) {
      top = Math.max(top, CARRIAGE_TOP + s.height);
    }
  });
  return top;
}

function specimenUnder(cx) {
  let best = 0, bestDist = Infinity;
  STOPS.forEach((st, i) => {
    const d = Math.abs(cx - st);
    if (d < bestDist) { bestDist = d; best = i; }
  });
  return best;
}

let x = START_X, target = START_X;
let tip = { at: REST_TOP, rate: 0 };
let frame = 0, last = 0, clock = 0, touring = !still.matches, visible = false, idleTimer = 0;
const tourOrder = [3, 0, 1, 2];
const tourAt = (t) => STOPS[tourOrder[Math.floor(t / 2.4) % tourOrder.length]];

function renderFrame() {
  const dx = x - START_X;
  const carTf = translateAlong(P, [dx, 0, 0]);
  carriageParts.forEach((el) => el.setAttribute("transform", carTf));

  const dz = tip.at - REST_TOP;
  const plgTf = translateAlong(P, [0, 0, dz]);
  plungerParts.forEach((el) => el.setAttribute("transform", plgTf));

  const estNodes = Math.max(0, ((tip.at - CARRIAGE_TOP) / 18) * 12);
  needle.setAttribute("d", needleAt(estNodes / 16));

  const idx = specimenUnder(x);
  const s = SPECIMENS[idx];
  const tag = idx === 3 ? "eager ast" : idx === 0 ? "lazy skip" : "preparse";
  const text = tag + " · " + s.tokens + " tok · " + Math.round(estNodes) + " nodes";
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", String(Math.round(estNodes)));
}

function tick(now) {
  const dt = last ? Math.min((now - last) / 1000, 1 / 30) : 1 / 60;
  last = now;
  const calm = still.matches;
  if (touring) { clock += dt; target = tourAt(clock); }
  x = calm ? target : x + (target - x) * (1 - Math.exp(-dt / 0.24));
  if (Math.abs(target - x) < 0.01) x = target;

  const want = heightUnder(x);
  const stiff = 420, drag = calm ? 2 * Math.sqrt(420) : 28;
  for (let i = 0; i < 4; i++) {
    tip.rate += ((want - tip.at) * stiff - tip.rate * drag) * (dt / 4);
    tip.at += tip.rate * (dt / 4);
  }
  if (Math.abs(want - tip.at) < 0.005 && Math.abs(tip.rate) < 0.005) {
    tip.at = want;
    tip.rate = 0;
  }
  renderFrame();
  const settled = !touring && x === target && tip.rate === 0 && tip.at === want;
  frame = visible && !settled ? requestAnimationFrame(tick) : 0;
}

const run = () => { if (!frame && visible) { last = 0; frame = requestAnimationFrame(tick); } };
const steer = (next) => {
  touring = false;
  target = clamp(next, REACH[0], REACH[1]);
  const s = SPECIMENS[specimenUnder(target)];
  stage.setAttribute("aria-valuetext", s.mode + ": " + s.tokens + " tokens, " + s.astNodes + " AST nodes");
  clearTimeout(idleTimer);
  idleTimer = setTimeout(() => { touring = !still.matches; clock = 0; run(); }, 3600);
  run();
};

new IntersectionObserver((entries) => {
  visible = entries[entries.length - 1].isIntersecting;
  if (visible) run();
}, { rootMargin: "120px 0px" }).observe(stage);

stage.addEventListener("pointermove", (ev) => {
  const box = svg.getBoundingClientRect();
  const share = clamp(((ev.clientX - box.left) / box.width - 0.18) / 0.64, 0, 1);
  steer(REACH[1] - share * (REACH[1] - REACH[0]));
});
stage.addEventListener("click", () => {
  const cur = specimenUnder(touring ? x : target);
  steer(STOPS[(cur + 1) % STOPS.length]);
});
stage.addEventListener("keydown", (ev) => {
  const cur = specimenUnder(touring ? x : target);
  if (ev.key === "ArrowRight" || ev.key === "ArrowUp") { ev.preventDefault(); steer(STOPS[Math.min(STOPS.length - 1, cur + 1)]); }
  else if (ev.key === "ArrowLeft" || ev.key === "ArrowDown") { ev.preventDefault(); steer(STOPS[Math.max(0, cur - 1)]); }
  else if (ev.key === " " || ev.key === "Enter") { ev.preventDefault(); steer(STOPS[cur === 3 ? 0 : 3]); }
  else if (ev.key === "Home") { ev.preventDefault(); steer(STOPS[0]); }
  else if (ev.key === "End") { ev.preventDefault(); steer(STOPS[STOPS.length - 1]); }
});
renderFrame();
`;

const info = B.writePages({
  slug: "anatomy-01-parser",
  fig: "Fig 1A",
  title: "Scanner & PreParser Diverter",
  hint: "drag or arrows · space toggles",
  readout: "eager ast · 14 tok · 12 nodes",
  keys: [
    { mark: "lit", label: "Eager AST block & probe" },
    { mark: "raised", label: "Scanner optical bridge" },
    { mark: "edge", label: "AST zone allocation dial" },
  ],
  caption:
    "V8 avoids building full ASTs for cold inner functions: Scanner feeds a single-token stream while PreParser emits thin scope shells (6–9 tokens skipped) until a hot call forces eager AST allocation.",
  svg,
  liveScript,
  ariaLabel:
    "V8 Scanner and Lazy/Eager Parser benchtop rig. Glide horizontally or use Left and Right arrow keys to inspect four JS source specimens; press Space to toggle between Lazy PreParser and Eager AST.",
});

if (!process.argv.includes("--audit")) {
  console.log(`built ${info.slug ?? "anatomy-01-parser"} (${info.solids} solids, ${info.items} items)`);
}
