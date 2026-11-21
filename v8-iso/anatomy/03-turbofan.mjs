import * as k from "../kit/iso-kit.mjs";
import { createBench } from "./bench.mjs";

const WIDTH = 620;
const HEIGHT = 390;

const PLATE = { x: -138, y: -68, w: 276, d: 136, r: 8 };
const PLATE_H = 12;
const FOOT_H = 5;

const PROBE_X = 4;
const PROBE_Y = -6;

// Real V8 Maglev / TurboFan speculative guard & deoptimization states
const JIT_CASES = [
  {
    id: "smi-fast",
    tag: "smi fast-path",
    guard: "CheckSmi ok",
    ns: 1.0,
    height: 5.5,
  },
  {
    id: "map-fast",
    tag: "monomorphic jit",
    guard: "CheckMaps#1 ok",
    ns: 1.4,
    height: 8.5,
  },
  {
    id: "float-deopt",
    tag: "deopt: heapnum",
    guard: "CheckSmi fail",
    ns: 34.0,
    height: 15.5,
  },
  {
    id: "map-bailout",
    tag: "eager bailout",
    guard: "WrongMap#9 → Ignition",
    ns: 48.0,
    height: 21.0,
  },
];

const CARRIAGE_Z = 3;
const CARRIAGE_TOP = 8;
const BLOCK_W = 10;
const BLOCK_STEP = 12;
const FIRST_LOCAL_X = -23;

const STOPS = JIT_CASES.map(
  (_, idx) => PROBE_X - (FIRST_LOCAL_X + BLOCK_STEP * idx + BLOCK_W / 2),
);
const REACH = [Math.min(...STOPS) - 3, Math.max(...STOPS) + 3];

const P = k.fitProjection(
  [
    ...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0),
    [-128, -36, 40],
    [-26, -38, 70],
    [124, 34, 84],
  ],
  WIDTH,
  HEIGHT,
  { pad: 28, azimuth: 44, elevation: 30 },
);

const B = createBench(P);
const { at, Ln, Dots, slab, cyl, benchPlate, rulerStrip, labelPlate, knurledKnob, dialGauge, cable } = B;

// 1. Bench plate, ruler & single engraved nameplate
benchPlate(PLATE, PLATE_H, FOOT_H);
rulerStrip("stand.ruler", { x: -126, y: 50, w: 174, d: 7, r: 1 }, 0, 0.6);
labelPlate("stand.label", { x: 58, y: 49, w: 68, d: 9, r: 1.2 }, 0, 0.8, { text: "CHECKMAPS · JIT" });

// 2. Left Hot-Loop Profiling Flywheel & Tier-Up Governor
slab("fly.base", { x: -128, y: -36, w: 46, d: 52, r: 3.5 }, 0, 11, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5.5 });
const flyTicks = k.radialTicks(-105, -10, 13.5, 48, 6, 18, [1.2, 2.5], P);
cyl("fly.wheel", -105, -10, 16, 11, 7, { tone: "hi", crease: "lo" }, {
  steps: 56,
  bevel: 0.7,
  knurlCount: 64,
  extra:
    Ln(k.ring(-105, -10, 14, 18, P, 56), { tone: "lo" }) +
    Ln(flyTicks.minor, { tone: "lo" }) +
    Ln(flyTicks.major, { tone: "mid" }),
});
cyl("fly.boss", -105, -10, 5.5, 18, 4, { tone: "mid" }, { steps: 28 });
knurledKnob("fly.governor", -105, -10, 3.8, 22, 3.6, { count: 22, pointerAngle: -0.9 });

slab("gov.pedestal", { x: -124, y: 20, w: 32, d: 22, r: 2.5 }, 0, 7, { tone: "mid" }, { steps: 4, bevel: 0.5 });
knurledKnob("gov.knob", -108, 31, 6.0, 7, 4.5, { count: 28, pointerAngle: 0.5 });

// 3. Twin Speculative Value-Tag Rails & End Stops
[-21, 9].forEach((ry, idx) => {
  slab(`rail.bar${idx}`, { x: -70, y: ry, w: 122, d: 5, r: 1 }, 0, 3, { tone: "mid" }, {
    steps: 3,
    bevel: 0.4,
    extra: Dots([-62, -22, 18, 44].map((rx) => at([rx, ry + 2.5, 3])), { size: 0.4 }),
  });
});
[-75, 52].forEach((sx, idx) => {
  slab(`rail.stop${idx}`, { x: sx, y: -24, w: 5, d: 41, r: 1.2 }, 0, 7, { tone: "mid" }, {
    steps: 3,
    bevel: 0.5,
    extra: Dots([at([sx + 2.5, -19, 7]), at([sx + 2.5, 12, 7])], { size: 0.45 }),
  });
});
[-42, -2].forEach((tx, idx) => {
  slab(`rail.tie${idx}`, { x: tx, y: -16, w: 6, d: 25, r: 0.8 }, 0, 1.5, { tone: "lo", crease: "none" }, { steps: 2, bevel: 0 });
});

// 4. CheckMaps Speculative Caliper Gantry Arch (x = -41..-25)
slab("caliper.backFoot", { x: -41, y: -39, w: 16, d: 14, r: 2 }, 0, 4, { tone: "lo" }, { steps: 3, bevel: 0.4 });
slab("caliper.backPost", { x: -39, y: -37, w: 12, d: 10, r: 1.8 }, 4, 41, { tone: "mid" }, { steps: 3, bevel: 0.5, seamZ: 24 });

slab("caliper.frontFoot", { x: -41, y: 17, w: 16, d: 14, r: 2 }, 0, 4, { tone: "lo" }, { steps: 3, bevel: 0.4 });
slab("caliper.frontPost", { x: -39, y: 19, w: 12, d: 10, r: 1.8 }, 4, 41, { tone: "mid" }, { steps: 3, bevel: 0.5, seamZ: 24 });

slab("caliper.arch", { x: -41, y: -38, w: 16, d: 68, r: 2.5 }, 45, 7, { tone: "mid" }, {
  steps: 4,
  bevel: 0.7,
  extra: Dots([at([-33, -33, 52]), at([-33, 25, 52])], { size: 0.48 }),
});
cyl("caliper.jaw", -33, -6, 4.2, 36, 9, { tone: "hi" }, { steps: 28, seamZs: [39] });
cyl("caliper.sleeve", -33, -6, 6.8, 52, 6, { tone: "mid" }, { steps: 34, seamZs: [55] });
knurledKnob("caliper.thimble", -33, -6, 5.2, 58, 5.5, { count: 28, pointerAngle: 1.2, tone: "hi" });

// 5. Moving Tagged-Value Specimen Carriage (starts at Bailout idx = 3 for dramatic contrast)
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

JIT_CASES.forEach((c, idx) => {
  const bx = startX + FIRST_LOCAL_X + BLOCK_STEP * idx;
  const bPlan = { x: bx, y: -14, w: BLOCK_W, d: 16, r: 1.1 };
  const isBailout = idx === 3;
  slab(`carriage.tag${idx}`, bPlan, CARRIAGE_TOP, c.height, { tone: "hi", crease: "lo", lit: isBailout }, {
    steps: 3,
    bevel: 0.45,
    attrs: 'data-part="carriage"',
    extra: Ln(k.planOutline(k.insetPlan(bPlan, 1.8), CARRIAGE_TOP + c.height, P, 3), { tone: "faint" }),
  });
});

// 6. Right Deoptimizer Bailout Stand, Reconstructed Ignition Frame Stack & Latency Dial
slab("deopt.base", { x: 60, y: -38, w: 64, d: 72, r: 4 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5 });
slab("deopt.deck", { x: 64, y: -34, w: 56, d: 64, r: 3 }, 10, 6, { tone: "mid" }, {
  steps: 5,
  bevel: 0.6,
  extra: Ln(k.planOutline(k.insetPlan({ x: 64, y: -34, w: 56, d: 64, r: 3 }, 3), 16, P, 4), { tone: "faint" }),
});

// 4-frame Deoptimizer Translation Stack on front-right of deck
for (let f = 0; f < 4; f++) {
  const z0 = 16 + f * 4.0;
  const fPlan = { x: 70, y: 4, w: 28, d: 20, r: 1.4 };
  slab(`deopt.frame${f}`, fPlan, z0, 4.0, { tone: f === 3 ? "hi" : "mid" }, {
    steps: 3,
    bevel: 0.35,
    extra: f === 3 ? Dots([at([74, 8, z0 + 4]), at([94, 8, z0 + 4]), at([74, 20, z0 + 4]), at([94, 20, z0 + 4])], { size: 0.4 }) : "",
  });
}
knurledKnob("deopt.latchKnob", 108, 14, 5.4, 16, 4.5, { count: 26, pointerAngle: 1.5 });

// Column, Arm, Bailout Trip Plunger & Dial Gauge
const POST_X = 100;
const POST_Y = PROBE_Y;
cyl("deopt.collar", POST_X, POST_Y, 6.2, 16, 4, { tone: "lo" }, { steps: 28 });
cyl("deopt.post", POST_X, POST_Y, 3.8, 20, 35, { tone: "mid", crease: "none" }, { steps: 28, seamZs: [32, 45] });
slab("deopt.clamp", { x: POST_X - 8, y: POST_Y - 8, w: 16, d: 16, r: 2.5 }, 55, 8, { tone: "mid" }, { steps: 4, bevel: 0.6 });

const ARM = { x: PROBE_X - 10, y: POST_Y - 5, w: POST_X - PROBE_X + 18, d: 10, r: 2 };
slab("deopt.arm", ARM, 63, 5, { tone: "mid" }, {
  steps: 4,
  bevel: 0.5,
  extra: Dots([at([ARM.x + 4, POST_Y, 68]), at([POST_X - 10, POST_Y, 68])], { size: 0.45 }),
});
cyl("deopt.postCap", POST_X, POST_Y, 4.6, 68, 3, { tone: "hi" }, { steps: 28, bevel: 0.4 });

cyl("probe.gland", PROBE_X, PROBE_Y, 3.6, 51, 12, { tone: "mid" }, { steps: 24, seamZs: [56] });
const restTop = CARRIAGE_TOP + JIT_CASES[REST_IDX].height; // 29
cyl("probe.shoe", PROBE_X, PROBE_Y, 2.8, restTop, 2.4, { tone: "hi", lit: true }, {
  steps: 22,
  attrs: 'data-part="plunger"',
});
cyl("probe.stem", PROBE_X, PROBE_Y, 1.5, restTop + 2.4, 51 - (restTop + 2.4), { tone: "hi", crease: "none", lit: true }, {
  steps: 18,
  attrs: 'data-part="plunger"',
});

const DIAL_R = 18.5;
dialGauge("deopt.dial", PROBE_X, PROBE_Y, DIAL_R, 68, 9.5, {
  count: 48,
  every: 6,
  needlePart: "needle",
  startTurn: 0.78,
});

// 7. Twin parallel bailout signal cables in horizontal lanes (y = 22 and y = 28)
cable(
  "deopt.lane0",
  [
    [-25, 21, 2],
    [0, 21, 2],
    [20, 28, 2],
    [42, 21, 2],
    [60, 21, 2],
  ],
  0.52,
  { tone: "mid", bend: 5 },
);
cable(
  "deopt.lane1",
  [
    [-25, 27, 2],
    [-2, 27, 2],
    [20, 35, 2],
    [44, 27, 2],
    [60, 27, 2],
  ],
  0.52,
  { tone: "lo", bend: 5 },
);

const svg = B.assembleSvg({
  width: WIDTH,
  height: HEIGHT,
  label:
    "Isometric V8 Maglev and TurboFan speculative JIT gate and deoptimization bailout rig. A hot-loop flywheel feeds tagged specimens through a CheckMaps caliper arch toward a deoptimizer frame-translation stack. Matching Smi and Map tags pass low under the trip plunger; polymorphic HeapNumber or wrong-Map tags lift the bailout plunger and swing the latency dial.",
});

const liveScript = `
const P = ${JSON.stringify(P)};
const JIT_CASES = ${JSON.stringify(JIT_CASES)};
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
    ${68 + 9.5 + 0.2},
    P
  );
};

function heightUnder(cx) {
  let top = CARRIAGE_TOP;
  JIT_CASES.forEach((s, i) => {
    const from = cx + FIRST_LOCAL + BLOCK_STEP * i;
    const to = from + BLOCK_W;
    if (to > PROBE_X - TIP_R && from < PROBE_X + TIP_R) {
      top = Math.max(top, CARRIAGE_TOP + s.height);
    }
  });
  return top;
}

function caseUnder(cx) {
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
const tourOrder = [0, 1, 2, 3];
const tourAt = (t) => STOPS[tourOrder[Math.floor(t / 2.3) % tourOrder.length]];

function renderFrame() {
  const dx = x - START_X;
  const carTf = translateAlong(P, [dx, 0, 0]);
  carriageParts.forEach((el) => el.setAttribute("transform", carTf));

  const dz = tip.at - REST_TOP;
  const plgTf = translateAlong(P, [0, 0, dz]);
  plungerParts.forEach((el) => el.setAttribute("transform", plgTf));

  const norm = clamp((tip.at - (CARRIAGE_TOP + 5.5)) / 15.5, 0, 1);
  const turn = 0.06 + norm * 0.72;
  needle.setAttribute("d", needleAt(turn));

  const idx = caseUnder(x);
  const c = JIT_CASES[idx];
  const ns = (1.0 + norm * 47.0).toFixed(1);
  const text = c.tag + " · " + ns + " ns";
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", String(Math.round( parseFloat(ns) )));
}

function tick(now) {
  const dt = last ? Math.min((now - last) / 1000, 1 / 30) : 1 / 60;
  last = now;
  const calm = still.matches;
  if (touring) { clock += dt; target = tourAt(clock); }
  x = calm ? target : x + (target - x) * (1 - Math.exp(-dt / 0.22));
  if (Math.abs(target - x) < 0.01) x = target;

  const want = heightUnder(x);
  const stiff = 460, drag = calm ? 2 * Math.sqrt(460) : 26;
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
  const c = JIT_CASES[caseUnder(target)];
  stage.setAttribute("aria-valuetext", c.tag + " (" + c.guard + "), " + c.ns + " ns");
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
  const cur = caseUnder(touring ? x : target);
  steer(STOPS[(cur + 1) % STOPS.length]);
});
stage.addEventListener("keydown", (ev) => {
  const cur = caseUnder(touring ? x : target);
  if (ev.key === "ArrowRight" || ev.key === "ArrowUp") { ev.preventDefault(); steer(STOPS[Math.min(STOPS.length - 1, cur + 1)]); }
  else if (ev.key === "ArrowLeft" || ev.key === "ArrowDown") { ev.preventDefault(); steer(STOPS[Math.max(0, cur - 1)]); }
  else if (ev.key === " " || ev.key === "Enter") { ev.preventDefault(); steer(STOPS[cur === 0 ? 3 : 0]); }
  else if (ev.key === "Home") { ev.preventDefault(); steer(STOPS[0]); }
  else if (ev.key === "End") { ev.preventDefault(); steer(STOPS[STOPS.length - 1]); }
});
renderFrame();
`;

const info = B.writePages({
  slug: "anatomy-03-turbofan",
  fig: "Fig 3A",
  title: "TurboFan Speculative Gate & Bailout",
  hint: "drag or arrows · space trips deopt",
  readout: "eager bailout · 48.0 ns",
  keys: [
    { mark: "lit", label: "Bailout trip cam & plunger" },
    { mark: "raised", label: "CheckMaps caliper & frame stack" },
    { mark: "edge", label: "Execution latency dial" },
  ],
  caption:
    "TurboFan and Maglev lower hot operations under CheckSmi and CheckMaps guards (1.0 ns fast path). An unexpected shape trips eager deoptimization, reconstructing Ignition stack frames instead of reading an object at the wrong offset.",
  svg,
  liveScript,
  ariaLabel:
    "V8 TurboFan Speculative JIT Gate and Deopt Bailout rig. Glide or use Left/Right arrows to test Smi fast-path (1.0 ns) versus wrong-Map eager deopt bailout (48.0 ns); press Space to toggle.",
});

if (!process.argv.includes("--audit")) {
  console.log(`built anatomy-03-turbofan (${info.solids} solids, ${info.items} items)`);
}
