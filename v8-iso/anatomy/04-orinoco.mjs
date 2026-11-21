import * as k from "../kit/iso-kit.mjs";
import { createBench } from "./bench.mjs";

const WIDTH = 620;
const HEIGHT = 390;

const PLATE = { x: -138, y: -68, w: 276, d: 136, r: 8 };
const PLATE_H = 12;
const FOOT_H = 5;

const PROBE_X = -6;
const PROBE_Y = -8;

// Real V8 HiddenClass (Map) & Orinoco Young/Old GC tricolor compaction phases
const GC_PHASES = [
  {
    id: "nursery",
    tag: "nursery fragmented",
    liveBytes: 24,
    usedBytes: 48,
    height: 19.5,
  },
  {
    id: "gray-mark",
    tag: "tricolor gray mark",
    liveBytes: 24,
    usedBytes: 40,
    height: 15.0,
  },
  {
    id: "scavenge",
    tag: "semi-space copy",
    liveBytes: 24,
    usedBytes: 31,
    height: 10.5,
  },
  {
    id: "compacted",
    tag: "to-space compact",
    liveBytes: 24,
    usedBytes: 24,
    height: 6.0,
  },
];

const CARRIAGE_Z = 3;
const CARRIAGE_TOP = 8;
const BLOCK_W = 10;
const BLOCK_STEP = 12;
const FIRST_LOCAL_X = -23;

const STOPS = GC_PHASES.map(
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
  { pad: 28, azimuth: 42, elevation: 30 },
);

const B = createBench(P);
const { at, Ln, Dots, slab, cyl, benchPlate, rulerStrip, labelPlate, knurledKnob, dialGauge, cable } = B;

// 1. Surface plate, ruler & single engraved nameplate
benchPlate(PLATE, PLATE_H, FOOT_H);
rulerStrip("stand.ruler", { x: -126, y: 50, w: 172, d: 7, r: 1 }, 0, 0.6);
labelPlate("stand.label", { x: 56, y: 49, w: 70, d: 9, r: 1.2 }, 0, 0.8, { text: "MAP · ORINOCO" });

// 2. Left HiddenClass (Map0 -> Map1 -> Map2) Transition Staircase & Root Handle Selector
slab("map.base", { x: -128, y: -38, w: 48, d: 68, r: 3.5 }, 0, 9, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 4.5 });

// 3 ascending Map descriptor blocks (+0, +4, +8 in-object field transitions)
[
  { h: 6, label: "m0" },
  { h: 11, label: "m1" },
  { h: 16, label: "m2" },
].forEach((m, idx) => {
  const mx = -123 + idx * 13;
  const mPlan = { x: mx, y: -32, w: 11, d: 24, r: 1.2 };
  slab(`map.step${idx}`, mPlan, 9, m.h, { tone: idx === 2 ? "hi" : "mid", crease: "lo" }, {
    steps: 3,
    bevel: 0.45,
    extra:
      Ln(k.planOutline(k.insetPlan(mPlan, 1.8), 9 + m.h, P, 3), { tone: "faint" }) +
      Dots([at([mx + 5.5, -27, 9 + m.h]), at([mx + 5.5, -13, 9 + m.h])], { size: 0.42 }),
  });
});

// Root-set rotary handle turret at front-left of Map base
cyl("root.collar", -104, 12, 10.5, 9, 5, { tone: "lo" }, { steps: 36 });
knurledKnob("root.knob", -104, 12, 7.2, 14, 5, { count: 32, pointerAngle: 0.35, tone: "hi" });

// 3. Twin Heap Evacuation Rails & End Stops
[-21, 9].forEach((ry, idx) => {
  slab(`rail.bar${idx}`, { x: -68, y: ry, w: 120, d: 5, r: 1 }, 0, 3, { tone: "mid" }, {
    steps: 3,
    bevel: 0.4,
    extra: Dots([-60, -20, 18, 44].map((rx) => at([rx, ry + 2.5, 3])), { size: 0.4 }),
  });
});
[-73, 52].forEach((sx, idx) => {
  slab(`rail.stop${idx}`, { x: sx, y: -24, w: 5, d: 41, r: 1.2 }, 0, 7, { tone: "mid" }, {
    steps: 3,
    bevel: 0.5,
    extra: Dots([at([sx + 2.5, -19, 7]), at([sx + 2.5, 12, 7])], { size: 0.45 }),
  });
});
[-40, 0].forEach((tx, idx) => {
  slab(`rail.tie${idx}`, { x: tx, y: -16, w: 6, d: 25, r: 0.8 }, 0, 1.5, { tone: "lo", crease: "none" }, { steps: 2, bevel: 0 });
});

// 4. Moving Tricolor Mark-Compact Heap Carriage (starts at Compacted To-Space idx = 3)
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

GC_PHASES.forEach((ph, idx) => {
  const bx = startX + FIRST_LOCAL_X + BLOCK_STEP * idx;
  const bPlan = { x: bx, y: -14, w: BLOCK_W, d: 16, r: 1.1 };
  const isCompacted = idx === 3;
  slab(`carriage.heap${idx}`, bPlan, CARRIAGE_TOP, ph.height, { tone: "hi", crease: "lo", lit: isCompacted }, {
    steps: 3,
    bevel: 0.45,
    attrs: 'data-part="carriage"',
    extra: Ln(k.planOutline(k.insetPlan(bPlan, 1.8), CARRIAGE_TOP + ph.height, P, 3), { tone: "faint" }),
  });
});

// 5. Right Orinoco Semi-Space Reservoirs (From-Space / To-Space) & Heap Occupancy Dial
slab("gc.base", { x: 60, y: -38, w: 64, d: 72, r: 4 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5 });
slab("gc.deck", { x: 64, y: -34, w: 56, d: 64, r: 3 }, 10, 6, { tone: "mid" }, {
  steps: 5,
  bevel: 0.6,
  extra: Ln(k.planOutline(k.insetPlan({ x: 64, y: -34, w: 56, d: 64, r: 3 }, 3), 16, P, 4), { tone: "faint" }),
});

// Twin Semi-Space Collector Cylinders (From-Space & To-Space) on front-right deck
[
  [78, 14, "fromCan"],
  [102, 14, "toCan"],
].forEach(([cx, cy, cname], idx) => {
  cyl(`gc.${cname}`, cx, cy, 8.2, 16, 13, { tone: idx === 1 ? "hi" : "mid" }, {
    steps: 36,
    bevel: 0.5,
    seamZs: [20, 25],
  });
  cyl(`gc.${cname}Cap`, cx, cy, 5.2, 29, 2.4, { tone: "mid" }, {
    steps: 24,
    extra: Ln(k.ring(cx, cy, 3.0, 31.4, P, 20), { tone: "lo" }),
  });
});

// Gauge Column, Arm, Plunger & Heap Occupancy Dial
const POST_X = 98;
const POST_Y = PROBE_Y;
cyl("gc.collar", POST_X, POST_Y, 6.2, 16, 4, { tone: "lo" }, { steps: 28 });
cyl("gc.post", POST_X, POST_Y, 3.8, 20, 34, { tone: "mid", crease: "none" }, { steps: 28, seamZs: [32, 44] });
slab("gc.clamp", { x: POST_X - 8, y: POST_Y - 8, w: 16, d: 16, r: 2.5 }, 54, 8, { tone: "mid" }, { steps: 4, bevel: 0.6 });

const ARM = { x: PROBE_X - 10, y: POST_Y - 5, w: POST_X - PROBE_X + 18, d: 10, r: 2 };
slab("gc.arm", ARM, 62, 5, { tone: "mid" }, {
  steps: 4,
  bevel: 0.5,
  extra: Dots([at([ARM.x + 4, POST_Y, 67]), at([POST_X - 10, POST_Y, 67])], { size: 0.45 }),
});
cyl("gc.postCap", POST_X, POST_Y, 4.6, 67, 3, { tone: "hi" }, { steps: 28, bevel: 0.4 });

cyl("probe.gland", PROBE_X, PROBE_Y, 3.6, 48, 14, { tone: "mid" }, { steps: 24, seamZs: [53] });
const restTop = CARRIAGE_TOP + GC_PHASES[REST_IDX].height; // 14
cyl("probe.shoe", PROBE_X, PROBE_Y, 2.8, restTop, 2.4, { tone: "hi", lit: true }, {
  steps: 22,
  attrs: 'data-part="plunger"',
});
cyl("probe.stem", PROBE_X, PROBE_Y, 1.5, restTop + 2.4, 48 - (restTop + 2.4), { tone: "hi", crease: "none", lit: true }, {
  steps: 18,
  attrs: 'data-part="plunger"',
});

const DIAL_R = 18.0;
dialGauge("gc.dial", PROBE_X, PROBE_Y, DIAL_R, 67, 9.5, {
  count: 48,
  every: 6,
  needlePart: "needle",
  startTurn: 24 / 64,
});

// 6. Root-pointer bus cable in horizontal plane from Map base (x = -80) to GC base (x = 60)
cable(
  "gc.roots",
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
    "Isometric V8 HiddenClass transition rack and Orinoco tricolor scavenger press. Left holds three ascending Map offset descriptors and a root-set turret; centre slides four heap compaction states under a heap-occupancy dial gauge; right carries From-Space and To-Space collector cylinders.",
});

const liveScript = `
const P = ${JSON.stringify(P)};
const GC_PHASES = ${JSON.stringify(GC_PHASES)};
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
  GC_PHASES.forEach((s, i) => {
    const from = cx + FIRST_LOCAL + BLOCK_STEP * i;
    const to = from + BLOCK_W;
    if (to > PROBE_X - TIP_R && from < PROBE_X + TIP_R) {
      top = Math.max(top, CARRIAGE_TOP + s.height);
    }
  });
  return top;
}

function phaseUnder(cx) {
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

  const norm = clamp((tip.at - (CARRIAGE_TOP + 6)) / 13.5, 0, 1);
  const used = Math.round(24 + norm * 24);
  const reclaimed = 48 - used;
  needle.setAttribute("d", needleAt(used / 64));

  const idx = phaseUnder(x);
  const ph = GC_PHASES[idx];
  const text = ph.tag + " · " + used + " B (" + reclaimed + " B freed)";
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", String(used));
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
  const ph = GC_PHASES[phaseUnder(target)];
  stage.setAttribute("aria-valuetext", ph.tag + ": " + ph.usedBytes + " bytes occupied");
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
  const cur = phaseUnder(target);
  steer(STOPS[(cur + 1) % STOPS.length]);
});
stage.addEventListener("keydown", (ev) => {
  const cur = phaseUnder(target);
  if (ev.key === "ArrowRight" || ev.key === "ArrowUp") { ev.preventDefault(); steer(STOPS[Math.min(STOPS.length - 1, cur + 1)]); }
  else if (ev.key === "ArrowLeft" || ev.key === "ArrowDown") { ev.preventDefault(); steer(STOPS[Math.max(0, cur - 1)]); }
  else if (ev.key === " " || ev.key === "Enter") { ev.preventDefault(); steer(STOPS[cur === 3 ? 0 : 3]); }
  else if (ev.key === "Home") { ev.preventDefault(); steer(STOPS[0]); }
  else if (ev.key === "End") { ev.preventDefault(); steer(STOPS[STOPS.length - 1]); }
});
renderFrame();
`;

const info = B.writePages({
  slug: "anatomy-04-orinoco",
  fig: "Fig 4A",
  title: "HiddenClass Rack & Orinoco Scavenger",
  hint: "drag or arrows · space compacts heap",
  readout: "to-space compact · 24 B (24 B freed)",
  keys: [
    { mark: "lit", label: "Compacted To-Space block & probe" },
    { mark: "raised", label: "Map transition steps & semi-spaces" },
    { mark: "edge", label: "Heap byte occupancy dial" },
  ],
  caption:
    "HiddenClass Maps assign fixed in-object field offsets (+0, +4, +8) while Orinoco's tricolor scavenger evacuates reachable gray/black objects into contiguous To-Space, reclaiming dead Nursery bytes in a single sweep.",
  svg,
  liveScript,
  ariaLabel:
    "V8 HiddenClass and Orinoco Garbage Collector rig. Glide or use Left/Right arrows to step from fragmented Nursery (48 B) through tricolor marking to compacted To-Space (24 B); press Space to compact.",
});

if (!process.argv.includes("--audit")) {
  console.log(`built anatomy-04-orinoco (${info.solids} solids, ${info.items} items)`);
}
