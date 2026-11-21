import * as k from "../kit/iso-kit.mjs";
import { createBench } from "./bench.mjs";

const WIDTH = 620;
const HEIGHT = 390;

const PLATE = { x: -138, y: -68, w: 276, d: 136, r: 8 };
const PLATE_H = 12;
const FOOT_H = 5;

const PROBE_X = -6;
const PROBE_Y = -8;

// Real V8 Liftoff WebAssembly linear-memory 64 KiB page & guard-zone states
const WASM_OFFSETS = [
  {
    id: "page0",
    tag: "page 0 [0x0010]",
    status: "ok · +64 KiB margin",
    height: 6.0,
  },
  {
    id: "page1",
    tag: "page 1 [0x10040]",
    status: "ok · +128 KiB grown",
    height: 10.0,
  },
  {
    id: "edge",
    tag: "limit [0x1FFFC]",
    status: "ok · 0 B slack",
    height: 14.5,
  },
  {
    id: "guard-trap",
    tag: "guard trap [oob]",
    status: "trapped · 0 host B",
    height: 20.5,
  },
];

const CARRIAGE_Z = 3;
const CARRIAGE_TOP = 8;
const BLOCK_W = 10;
const BLOCK_STEP = 12;
const FIRST_LOCAL_X = -23;

const STOPS = WASM_OFFSETS.map(
  (_, idx) => PROBE_X - (FIRST_LOCAL_X + BLOCK_STEP * idx + BLOCK_W / 2),
);
const REACH = [Math.min(...STOPS) - 3, Math.max(...STOPS) + 3];

const P = k.fitProjection(
  [
    ...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0),
    [-128, -36, 40],
    [124, 34, 82],
  ],
  WIDTH,
  HEIGHT,
  { pad: 28, azimuth: 45, elevation: 30 },
);

const B = createBench(P);
const { at, Ln, Dots, slab, cyl, benchPlate, rulerStrip, labelPlate, knurledKnob, dialGauge, cable } = B;

// 1. Bench plate, 64 KiB page ruler & single engraved nameplate
benchPlate(PLATE, PLATE_H, FOOT_H);
rulerStrip("stand.ruler", { x: -126, y: 50, w: 172, d: 7, r: 1 }, 0, 0.6);
labelPlate("stand.label", { x: 56, y: 49, w: 70, d: 9, r: 1.2 }, 0, 0.8, { text: "LIFTOFF · 64K" });

// 2. Left LEB128 Binary Stream Capstans & Liftoff Single-Pass Stamping Feed
slab("leb.base", { x: -128, y: -36, w: 48, d: 64, r: 3.5 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5 });

[
  [-114, -14, "capstan0"],
  [-93, -14, "capstan1"],
].forEach(([cx, cy, cname], idx) => {
  cyl(`leb.${cname}`, cx, cy, 7.6, 10, 12, { tone: idx === 1 ? "hi" : "mid" }, {
    steps: 32,
    bevel: 0.5,
    seamZs: [14, 18],
  });
  knurledKnob(`leb.${cname}Nut`, cx, cy, 4.5, 22, 3.2, { count: 22, pointerAngle: idx ? -0.6 : 0.9 });
});

// memory.grow page-limit detent knob
knurledKnob("leb.growKnob", -104, 13, 6.8, 10, 4.8, { count: 30, pointerAngle: 0.2 });

// 3. Twin Linear-Memory Address Rails & Hard Guard-Zone End Stop
[-21, 9].forEach((ry, idx) => {
  slab(`rail.bar${idx}`, { x: -68, y: ry, w: 118, d: 5, r: 1 }, 0, 3, { tone: "mid" }, {
    steps: 3,
    bevel: 0.4,
    extra: Dots([-60, -20, 16, 42].map((rx) => at([rx, ry + 2.5, 3])), { size: 0.4 }),
  });
});
slab("rail.stopLeft", { x: -73, y: -24, w: 5, d: 41, r: 1.2 }, 0, 7, { tone: "mid" }, {
  steps: 3,
  bevel: 0.5,
  extra: Dots([at([-70.5, -19, 7]), at([-70.5, 12, 7])], { size: 0.45 }),
});
// Heavy machined Guard-Zone Mechanical Stop on the right
slab("rail.guardStop", { x: 50, y: -25, w: 7, d: 43, r: 1.4 }, 0, 11, { tone: "hi", crease: "lo" }, {
  steps: 3,
  bevel: 0.6,
  seamZ: 5.5,
  extra: Dots([at([53.5, -20, 11]), at([53.5, -3.5, 11]), at([53.5, 13, 11])], { size: 0.48 }),
});
[-40, 0].forEach((tx, idx) => {
  slab(`rail.tie${idx}`, { x: tx, y: -16, w: 6, d: 25, r: 0.8 }, 0, 1.5, { tone: "lo", crease: "none" }, { steps: 2, bevel: 0 });
});

// 4. Moving Linear-Memory Offset Carriage (starts at Page 0 idx = 0)
const REST_IDX = 0;
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

WASM_OFFSETS.forEach((wo, idx) => {
  const bx = startX + FIRST_LOCAL_X + BLOCK_STEP * idx;
  const bPlan = { x: bx, y: -14, w: BLOCK_W, d: 16, r: 1.1 };
  const isTrap = idx === 3;
  slab(`carriage.page${idx}`, bPlan, CARRIAGE_TOP, wo.height, { tone: "hi", crease: "lo", lit: isTrap }, {
    steps: 3,
    bevel: 0.45,
    attrs: 'data-part="carriage"',
    extra: Ln(k.planOutline(k.insetPlan(bPlan, 1.8), CARRIAGE_TOP + wo.height, P, 3), { tone: "faint" }),
  });
});

// 5. Right 4 GiB Virtual Guard-Zone Containment Barrier & Trap Interlock Dial
slab("wasm.base", { x: 60, y: -38, w: 64, d: 72, r: 4 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5 });
slab("wasm.deck", { x: 64, y: -34, w: 56, d: 64, r: 3 }, 10, 6, { tone: "mid" }, {
  steps: 5,
  bevel: 0.6,
  extra: Ln(k.planOutline(k.insetPlan({ x: 64, y: -34, w: 56, d: 64, r: 3 }, 3), 16, P, 4), { tone: "faint" }),
});

// Solid Guard-Page Isolation Wall on front-right of deck
const wallPlan = { x: 68, y: 4, w: 46, d: 20, r: 2 };
slab("wasm.guardWall", wallPlan, 16, 13, { tone: "hi", crease: "lo" }, {
  steps: 4,
  bevel: 0.6,
  seamZ: 22.5,
  extra:
    Ln(k.planOutline(k.insetPlan(wallPlan, 2.2), 29, P, 3), { tone: "faint" }) +
    Dots([at([72, 8, 29]), at([110, 8, 29]), at([72, 20, 29]), at([110, 20, 29])], { size: 0.45 }),
});

// Column, Arm, Interlock Plunger & Bounds Dial
const POST_X = 98;
const POST_Y = PROBE_Y;
cyl("wasm.collar", POST_X, POST_Y, 6.2, 16, 4, { tone: "lo" }, { steps: 28 });
cyl("wasm.post", POST_X, POST_Y, 3.8, 20, 34, { tone: "mid", crease: "none" }, { steps: 28, seamZs: [32, 44] });
slab("wasm.clamp", { x: POST_X - 8, y: POST_Y - 8, w: 16, d: 16, r: 2.5 }, 54, 8, { tone: "mid" }, { steps: 4, bevel: 0.6 });

const ARM = { x: PROBE_X - 10, y: POST_Y - 5, w: POST_X - PROBE_X + 18, d: 10, r: 2 };
slab("wasm.arm", ARM, 62, 5, { tone: "mid" }, {
  steps: 4,
  bevel: 0.5,
  extra: Dots([at([ARM.x + 4, POST_Y, 67]), at([POST_X - 10, POST_Y, 67])], { size: 0.45 }),
});
cyl("wasm.postCap", POST_X, POST_Y, 4.6, 67, 3, { tone: "hi" }, { steps: 28, bevel: 0.4 });

cyl("probe.gland", PROBE_X, PROBE_Y, 3.6, 49, 13, { tone: "mid" }, { steps: 24, seamZs: [54] });
const restTop = CARRIAGE_TOP + WASM_OFFSETS[REST_IDX].height; // 14
cyl("probe.shoe", PROBE_X, PROBE_Y, 2.8, restTop, 2.4, { tone: "hi", lit: true }, {
  steps: 22,
  attrs: 'data-part="plunger"',
});
cyl("probe.stem", PROBE_X, PROBE_Y, 1.5, restTop + 2.4, 49 - (restTop + 2.4), { tone: "hi", crease: "none", lit: true }, {
  steps: 18,
  attrs: 'data-part="plunger"',
});

const DIAL_R = 18.0;
dialGauge("wasm.dial", PROBE_X, PROBE_Y, DIAL_R, 67, 9.5, {
  count: 48,
  every: 6,
  needlePart: "needle",
  startTurn: 0.12,
});

// 6. Sandbox trap-line cable in horizontal plane
cable(
  "wasm.trapLine",
  [
    [-80, 24, 2],
    [-42, 24, 2],
    [-8, 33, 2],
    [30, 24, 2],
    [60, 24, 2],
  ],
  0.58,
  { tone: "mid", bend: 6 },
);

const svg = B.assembleSvg({
  width: WIDTH,
  height: HEIGHT,
  label:
    "Isometric V8 Liftoff WebAssembly baseline feeder and linear-memory guard-zone stop. Left holds twin LEB128 byte capstans and a memory.grow detent; centre slides four address blocks against a heavy guard-zone stop under a bounds-check interlock plunger and dial.",
});

const liveScript = `
const P = ${JSON.stringify(P)};
const WASM_OFFSETS = ${JSON.stringify(WASM_OFFSETS)};
const STOPS = ${JSON.stringify(STOPS)};
const REACH = ${JSON.stringify(REACH)};
const START_X = ${startX};
const REST_TOP = ${restTop};
const CARRIAGE_TOP = ${CARRIAGE_TOP};
const PROBE_X = ${PROBE_X};
const FIRST_LOCAL = ${FIRST_LOCAL_X};
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
  WASM_OFFSETS.forEach((s, i) => {
    const from = cx + FIRST_LOCAL + BLOCK_STEP * i;
    const to = from + BLOCK_W;
    if (to > PROBE_X - TIP_R && from < PROBE_X + TIP_R) {
      top = Math.max(top, CARRIAGE_TOP + s.height);
    }
  });
  return top;
}

function offsetUnder(cx) {
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
const tourAt = (t) => STOPS[Math.floor(t / 2.3) % STOPS.length];

function renderFrame() {
  const dx = x - START_X;
  const carTf = translateAlong(P, [dx, 0, 0]);
  carriageParts.forEach((el) => el.setAttribute("transform", carTf));

  const dz = tip.at - REST_TOP;
  const plgTf = translateAlong(P, [0, 0, dz]);
  plungerParts.forEach((el) => el.setAttribute("transform", plgTf));

  const norm = clamp((tip.at - (CARRIAGE_TOP + 6)) / 14.5, 0, 1);
  needle.setAttribute("d", needleAt(0.10 + norm * 0.72));

  const idx = offsetUnder(x);
  const w = WASM_OFFSETS[idx];
  const text = w.tag + " · " + w.status;
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", String(Math.round(norm * 100)));
}

function tick(now) {
  const dt = last ? Math.min((now - last) / 1000, 1 / 30) : 1 / 60;
  last = now;
  const calm = still.matches;
  if (touring) { clock += dt; target = tourAt(clock); }
  x = calm ? target : x + (target - x) * (1 - Math.exp(-dt / 0.23));
  if (Math.abs(target - x) < 0.01) x = target;

  const want = heightUnder(x);
  const stiff = 450, drag = calm ? 2 * Math.sqrt(450) : 28;
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
  const w = WASM_OFFSETS[offsetUnder(target)];
  stage.setAttribute("aria-valuetext", w.tag + ": " + w.status);
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
  const cur = offsetUnder(touring ? x : target);
  steer(STOPS[(cur + 1) % STOPS.length]);
});
stage.addEventListener("keydown", (ev) => {
  const cur = offsetUnder(touring ? x : target);
  if (ev.key === "ArrowRight" || ev.key === "ArrowUp") { ev.preventDefault(); steer(STOPS[Math.min(STOPS.length - 1, cur + 1)]); }
  else if (ev.key === "ArrowLeft" || ev.key === "ArrowDown") { ev.preventDefault(); steer(STOPS[Math.max(0, cur - 1)]); }
  else if (ev.key === " " || ev.key === "Enter") { ev.preventDefault(); steer(STOPS[cur === 3 ? 0 : 3]); }
  else if (ev.key === "Home") { ev.preventDefault(); steer(STOPS[0]); }
  else if (ev.key === "End") { ev.preventDefault(); steer(STOPS[STOPS.length - 1]); }
});
renderFrame();
`;

const info = B.writePages({
  slug: "anatomy-05-liftoff",
  fig: "Fig 5A",
  title: "Liftoff Feeder & Guard-Zone Sandbox",
  hint: "drag or arrows · space tests oob trap",
  readout: "page 0 [0x0010] · ok · +64 KiB margin",
  keys: [
    { mark: "lit", label: "Guard-zone OOB cam & trap probe" },
    { mark: "raised", label: "LEB128 capstans & guard wall" },
    { mark: "edge", label: "Bounds margin / trap dial" },
  ],
  caption:
    "Liftoff compiles WebAssembly stack opcodes in one pass while confining every linear-memory load inside 64 KiB pages and a 4 GiB virtual guard zone—out-of-bounds offsets trap cleanly before touching host memory.",
  svg,
  liveScript,
  ariaLabel:
    "V8 Liftoff WebAssembly Baseline Compiler and Guard-Zone Sandbox rig. Glide or use Left/Right arrows to probe in-bounds 64 KiB pages versus the out-of-bounds guard-zone trap; press Space to toggle.",
});

if (!process.argv.includes("--audit")) {
  console.log(`built anatomy-05-liftoff (${info.solids} solids, ${info.items} items)`);
}
