import * as k from "../kit/iso-kit.mjs";
import { createBench } from "./bench.mjs";

const WIDTH = 620;
const HEIGHT = 390;

const PLATE = { x: -136, y: -68, w: 272, d: 136, r: 8 };
const PLATE_H = 12;
const FOOT_H = 5;

const PROBE_X = -6;
const PROBE_Y = -6;

// Real V8 Ignition FeedbackVector Inline-Cache lattice states
const IC_STATES = [
  {
    id: "mono",
    label: "monomorphic",
    maps: 1,
    cycles: 4,
    op: "LdaNamedProperty [slot 0]",
    height: 6,
  },
  {
    id: "poly2",
    label: "polymorphic (2)",
    maps: 2,
    cycles: 11,
    op: "CompareMap ×2 → field",
    height: 10.5,
  },
  {
    id: "poly4",
    label: "polymorphic (4)",
    maps: 4,
    cycles: 18,
    op: "CompareMap ×4 → field",
    height: 15,
  },
  {
    id: "mega",
    label: "megamorphic",
    maps: 5,
    cycles: 29,
    op: "LoadIC_Megamorphic stub",
    height: 20,
  },
];

const CARRIAGE_Z = 3;
const CARRIAGE_TOP = 8;
const BLOCK_W = 10;
const BLOCK_STEP = 12;
const FIRST_LOCAL_X = -23;

const STOPS = IC_STATES.map(
  (_, idx) => PROBE_X - (FIRST_LOCAL_X + BLOCK_STEP * idx + BLOCK_W / 2),
);
const REACH = [Math.min(...STOPS) - 3, Math.max(...STOPS) + 3];

const P = k.fitProjection(
  [
    ...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0),
    [-126, -36, 40],
    [122, 32, 82],
  ],
  WIDTH,
  HEIGHT,
  { pad: 28, azimuth: 41, elevation: 30 },
);

const B = createBench(P);
const { at, Ln, Dots, slab, cyl, benchPlate, rulerStrip, labelPlate, knurledKnob, dialGauge, cable } = B;

// 1. Bench plate, ruler & single engraved nameplate
benchPlate(PLATE, PLATE_H, FOOT_H);
rulerStrip("stand.ruler", { x: -124, y: 50, w: 170, d: 7, r: 1 }, 0, 0.6);
labelPlate("stand.label", { x: 56, y: 49, w: 68, d: 9, r: 1.2 }, 0, 0.8, { text: "IGNITION · IC" });

// 2. Left Ignition 4-Register Bank (r0, r1, a0, acc) & Bytecode Cam Drum
slab("reg.base", { x: -126, y: -40, w: 50, d: 44, r: 3 }, 0, 9, { tone: "mid" }, { steps: 5, bevel: 0.8 });
const REG_HEIGHTS = [7, 9, 11, 15];
REG_HEIGHTS.forEach((rh, idx) => {
  const rx = -121 + idx * 10.5;
  const rPlan = { x: rx, y: -33, w: 8.8, d: 28, r: 1.1 };
  slab(`reg.slot${idx}`, rPlan, 9, rh, { tone: idx === 3 ? "hi" : "mid", crease: "lo" }, {
    steps: 3,
    bevel: 0.4,
    extra:
      Ln(k.planOutline(k.insetPlan(rPlan, 1.5), 9 + rh, P, 3), { tone: "faint" }) +
      Dots([at([rx + 4.4, -29, 9 + rh]), at([rx + 4.4, -9, 9 + rh])], { size: 0.4 }),
  });
});

// Bytecode Opcode Indexing Drum at front-left
slab("drum.pedestal", { x: -124, y: 8, w: 42, d: 36, r: 3 }, 0, 8, { tone: "mid" }, { steps: 4, bevel: 0.6 });
const drumTicks = k.radialTicks(-103, 26, 10.5, 36, 6, 17, [1.1, 2.3], P);
cyl("drum.body", -103, 26, 12.5, 8, 9, { tone: "hi", crease: "lo" }, {
  steps: 48,
  bevel: 0.6,
  knurlCount: 52,
  extra:
    Ln(k.ring(-103, 26, 10.8, 17, P, 48), { tone: "lo" }) +
    Ln(drumTicks.minor, { tone: "lo" }) +
    Ln(drumTicks.major, { tone: "mid" }),
});
knurledKnob("drum.hub", -103, 26, 4.4, 17, 3.8, { count: 24, pointerAngle: 0.8 });

// 3. Twin FeedbackVector IC Rails & End Stops
[-21, 9].forEach((ry, idx) => {
  slab(`rail.bar${idx}`, { x: -68, y: ry, w: 118, d: 5, r: 1 }, 0, 3, { tone: "mid" }, {
    steps: 3,
    bevel: 0.4,
    extra: Dots([-60, -20, 16, 42].map((rx) => at([rx, ry + 2.5, 3])), { size: 0.4 }),
  });
});
[-73, 50].forEach((sx, idx) => {
  slab(`rail.stop${idx}`, { x: sx, y: -24, w: 5, d: 41, r: 1.2 }, 0, 7, { tone: "mid" }, {
    steps: 3,
    bevel: 0.5,
    extra: Dots([at([sx + 2.5, -19, 7]), at([sx + 2.5, 12, 7])], { size: 0.45 }),
  });
});
[-38, 2].forEach((tx, idx) => {
  slab(`rail.tie${idx}`, { x: tx, y: -16, w: 6, d: 25, r: 0.8 }, 0, 1.5, { tone: "lo", crease: "none" }, { steps: 2, bevel: 0 });
});

// 4. Moving FeedbackVector 4-Slot IC Cam Carriage (starts at Monomorphic idx = 0)
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

IC_STATES.forEach((st, idx) => {
  const bx = startX + FIRST_LOCAL_X + BLOCK_STEP * idx;
  const bPlan = { x: bx, y: -14, w: BLOCK_W, d: 16, r: 1.1 };
  const isMono = idx === 0;
  slab(`carriage.ic${idx}`, bPlan, CARRIAGE_TOP, st.height, { tone: "hi", crease: "lo", lit: isMono }, {
    steps: 3,
    bevel: 0.45,
    attrs: 'data-part="carriage"',
    extra: Ln(k.planOutline(k.insetPlan(bPlan, 1.8), CARRIAGE_TOP + st.height, P, 3), { tone: "faint" }),
  });
});

// Carriage front indexing handle (stacked vertically on carriage bed)
cyl("carriage.knob", startX + 20, 9, 3.2, CARRIAGE_TOP, 4.2, { tone: "mid" }, {
  steps: 24,
  knurlCount: 20,
  attrs: 'data-part="carriage"',
});

// 5. Right Dispatch Latency Stand, Megamorphic Stub-Cache Pot & Cycle Dial
slab("ic.base", { x: 58, y: -38, w: 64, d: 70, r: 4 }, 0, 10, { tone: "mid" }, { steps: 5, bevel: 0.8, seamZ: 5 });
slab("ic.deck", { x: 62, y: -34, w: 56, d: 62, r: 3 }, 10, 6, { tone: "mid" }, {
  steps: 5,
  bevel: 0.6,
  extra: Ln(k.planOutline(k.insetPlan({ x: 62, y: -34, w: 56, d: 62, r: 3 }, 3), 16, P, 4), { tone: "faint" }),
});

// Global Stub-Cache Hash Pot on front-right of deck
cyl("stub.pot", 86, 12, 9.5, 16, 11, { tone: "mid" }, { steps: 40, bevel: 0.5, seamZs: [20, 24] });
cyl("stub.lid", 86, 12, 7.2, 27, 2.5, { tone: "hi" }, {
  steps: 32,
  bevel: 0.4,
  extra: Ln(k.ring(86, 12, 4.5, 29.5, P, 24), { tone: "lo" }),
});
knurledKnob("stub.trim", 107, 14, 4.8, 16, 4.2, { count: 24, pointerAngle: -0.7 });

// Main Gauge Column & Arm
const POST_X = 98;
const POST_Y = PROBE_Y;
cyl("ic.collar", POST_X, POST_Y, 6.2, 16, 4, { tone: "lo" }, { steps: 28 });
cyl("ic.post", POST_X, POST_Y, 3.8, 20, 34, { tone: "mid", crease: "none" }, { steps: 28, seamZs: [32, 44] });
slab("ic.clamp", { x: POST_X - 8, y: POST_Y - 8, w: 16, d: 16, r: 2.5 }, 54, 8, { tone: "mid" }, { steps: 4, bevel: 0.6 });

const ARM = { x: PROBE_X - 10, y: POST_Y - 5, w: POST_X - PROBE_X + 18, d: 10, r: 2 };
slab("ic.arm", ARM, 62, 5, { tone: "mid" }, {
  steps: 4,
  bevel: 0.5,
  extra: Dots([at([ARM.x + 4, POST_Y, 67]), at([POST_X - 10, POST_Y, 67])], { size: 0.45 }),
});
cyl("ic.postCap", POST_X, POST_Y, 4.6, 67, 3, { tone: "hi" }, { steps: 28, bevel: 0.4 });

// Plunger & Cycle-Cost Dial Indicator
cyl("probe.gland", PROBE_X, PROBE_Y, 3.6, 48, 14, { tone: "mid" }, { steps: 24, seamZs: [53] });
const restTop = CARRIAGE_TOP + IC_STATES[REST_IDX].height; // 14
cyl("probe.shoe", PROBE_X, PROBE_Y, 2.8, restTop, 2.4, { tone: "hi", lit: true }, {
  steps: 22,
  attrs: 'data-part="plunger"',
});
cyl("probe.stem", PROBE_X, PROBE_Y, 1.5, restTop + 2.4, 48 - (restTop + 2.4), { tone: "hi", crease: "none", lit: true }, {
  steps: 18,
  attrs: 'data-part="plunger"',
});

const DIAL_R = 18.5;
dialGauge("ic.dial", PROBE_X, PROBE_Y, DIAL_R, 67, 9.5, {
  count: 48,
  every: 6,
  needlePart: "needle",
  startTurn: IC_STATES[REST_IDX].cycles / 36,
});

// 6. Floor cable from Bytecode Drum pedestal right face (x = -82) to IC stand left face (x = 58)
cable(
  "ic.bus",
  [
    [-82, 26, 2],
    [-46, 26, 2],
    [-12, 34, 2],
    [28, 26, 2],
    [58, 26, 2],
  ],
  0.58,
  { tone: "mid", bend: 6 },
);

const svg = B.assembleSvg({
  width: WIDTH,
  height: HEIGHT,
  label:
    "Isometric V8 Ignition interpreter and FeedbackVector inline-cache turret. Left holds a four-register accumulator bank and bytecode indexing drum; centre carries a sliding four-state inline-cache cam block (monomorphic, polymorphic 2, polymorphic 4, megamorphic) under a dispatch-cycle dial gauge.",
});

const liveScript = `
const P = ${JSON.stringify(P)};
const IC_STATES = ${JSON.stringify(IC_STATES)};
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
  IC_STATES.forEach((s, i) => {
    const from = cx + FIRST_LOCAL + BLOCK_STEP * i;
    const to = from + BLOCK_W;
    if (to > PROBE_X - TIP_R && from < PROBE_X + TIP_R) {
      top = Math.max(top, CARRIAGE_TOP + s.height);
    }
  });
  return top;
}

function stateUnder(cx) {
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

  const cyc = 4 + ((tip.at - (CARRIAGE_TOP + 6)) / 14) * 25;
  needle.setAttribute("d", needleAt(Math.max(0.05, cyc / 36)));

  const idx = stateUnder(x);
  const s = IC_STATES[idx];
  const text = s.label + " · " + s.maps + (s.maps === 1 ? " map · " : " maps · ") + Math.round(Math.max(4, cyc)) + " cyc";
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", String(Math.round(Math.max(4, cyc))));
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
  const s = IC_STATES[stateUnder(target)];
  stage.setAttribute("aria-valuetext", s.label + ": " + s.maps + " maps, " + s.cycles + " dispatch cycles");
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
  const cur = stateUnder(touring ? x : target);
  steer(STOPS[(cur + 1) % STOPS.length]);
});
stage.addEventListener("keydown", (ev) => {
  const cur = stateUnder(touring ? x : target);
  if (ev.key === "ArrowRight" || ev.key === "ArrowUp") { ev.preventDefault(); steer(STOPS[Math.min(STOPS.length - 1, cur + 1)]); }
  else if (ev.key === "ArrowLeft" || ev.key === "ArrowDown") { ev.preventDefault(); steer(STOPS[Math.max(0, cur - 1)]); }
  else if (ev.key === " " || ev.key === "Enter") { ev.preventDefault(); steer(STOPS[(cur + 1) % STOPS.length]); }
  else if (ev.key === "Home") { ev.preventDefault(); steer(STOPS[0]); }
  else if (ev.key === "End") { ev.preventDefault(); steer(STOPS[STOPS.length - 1]); }
});
renderFrame();
`;

const info = B.writePages({
  slug: "anatomy-02-ignition",
  fig: "Fig 2A",
  title: "Ignition & Inline-Cache Turret",
  hint: "drag or arrows · step ic lattice",
  readout: "monomorphic · 1 map · 4 cyc",
  keys: [
    { mark: "lit", label: "Monomorphic fast slot & probe" },
    { mark: "raised", label: "Register bank & bytecode drum" },
    { mark: "edge", label: "Dispatch cycle indicator" },
  ],
  caption:
    "Ignition caches seen HiddenClass Maps inside a four-slot FeedbackVector: one shape dispatches in 4 cycles, two to four shapes walk linear CompareMap guards, and a fifth overflows to the megamorphic stub cache.",
  svg,
  liveScript,
  ariaLabel:
    "V8 Ignition interpreter and FeedbackVector Inline-Cache benchtop rig. Use Left/Right arrows or pointer to step from monomorphic (1 Map, 4 cycles) through polymorphic to megamorphic (5+ Maps, 29 cycles).",
});

if (!process.argv.includes("--audit")) {
  console.log(`built anatomy-02-ignition (${info.solids} solids, ${info.items} items)`);
}
