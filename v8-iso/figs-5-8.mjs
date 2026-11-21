import { writeCadFigure } from "./iso-cad.mjs";

export function buildFigs5To8() {
  // ==========================================================================
  // FIG 5: Ignition — Finned Cylindrical 24V Starter Motor, Gears & Fuel Rail
  // ==========================================================================
  writeCadFigure({
    slug: "fig-05-ignition",
    fig: "Fig 5",
    title: "Ignition · Cylindrical 24V Starter & 4-Nozzle Rail",
    hint: "crank 24v starter · step 4 fuel-injector nozzles · drag to orbit",
    initialReadout: "24v on · inj #2 Add · acc 43 · warm 1",
    ariaLabel:
      "3D isometric 24V cylindrical electric starter motor with radial cooling fins, piggyback cylindrical solenoid, meshing 12-tooth involute pinion and 24-tooth flywheel ring gear, and a cylindrical common bytecode rail feeding four curved fuel lines into conical injector nozzles.",
    footHelp:
      "Click parts or keys: <kbd>C</kbd> crank 24V starter · <kbd>Space</kbd> step bytecode injector · <kbd>1</kbd>–<kbd>3</kbd> fire <code>LdaSmi</code> / <code>Add</code> / <code>Star</code> · <kbd>K</kbd> cut ignition · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 36,
    elDeg: 27,
    sceneJs: `
const OPS = [
  { name: 'LdaSmi', fn: (s) => { s.acc = 21; } },
  { name: 'Add',    fn: (s) => { s.acc = s.acc + s.r0; } },
  { name: 'Star r0', fn: (s) => { s.r0 = s.acc; } },
  { name: 'Return', fn: (s) => { s.warm++; } },
];
const st = { running: true, pc: 1, acc: 43, r0: 22, warm: 1, gearDeg: 15 };
const KM = { c: 'crank', ' ': 'step', Enter: 'step', '1': 'i0', '2': 'i1', '3': 'i2', '4': 'i3', k: 'cut', Escape: 'cut' };

function fire(idx) {
  st.running = true;
  st.pc = idx % 4;
  OPS[st.pc].fn(st);
  st.gearDeg = (st.gearDeg + 28) % 360;
}

function act(k) {
  if (k === 'crank') { st.running = true; st.gearDeg = (st.gearDeg + 28) % 360; }
  else if (k === 'cut') st.running = false;
  else if (k === 'step') fire((st.pc + 1) % 4);
  else if (k === 'i0') fire(0);
  else if (k === 'i1') fire(1);
  else if (k === 'i2') fire(2);
  else if (k === 'i3') fire(3);
  redraw(false);
}

function buildScene(cad) {
  // 1. Horizontal Cylindrical 24V Starter Motor Barrel + 7 Radial Cooling Fins + Saddle Clamps!
  for (const sx of [-112, -56]) {
    cad.cyl([sx, 16, 0], [sx, 16, 26], 8, 6, { segs: 12, tone: 'dark' });
  }
  cad.revolve(
    [[-136, 0.5], [-132, 24], [-124, 29], [-36, 29], [-24, 21], [-12, 12], [-12, 0.5]],
    { axis: 'x', origin: [0, 16, 36], segs: 26, tone: st.running ? 'body' : 'dark', key: 'crank' }
  );
  // 7 Radial Stator Cooling Fin Rings along the cylindrical motor!
  for (let f = 0; f < 7; f++) {
    const fx = -116 + f * 12;
    cad.cyl([fx, 16, 36], [fx + 3.2, 16, 36], 33, 33, { segs: 24, holeR: 28.5, tone: 'hi', key: 'crank' });
  }

  // 2. Piggyback Cylindrical 24V Starter Solenoid + Copper Jumper Busbar!
  cad.cyl([-114, 16, 75], [-46, 16, 75], 14, 14, { segs: 22, tone: st.running ? 'hi' : 'body', liveStroke: st.running, key: 'crank' });
  cad.sweepTube([[-118, 16, 75], [-128, 16, 62], [-122, 16, 52]], 2.4, { cornerR: 6, tone: 'hi' });
  // Solenoid Engagement Fork plunging down to nose cone
  cad.sweepTube([[-46, 16, 75], [-26, 16, 56], [-10, 16, 38]], 2.2, { cornerR: 6, tone: 'hi' });

  // 3. Meshing 12-Tooth Starter Pinion Gear + Large 22-Tooth Flywheel Ring Gear!
  const gRad = (st.gearDeg * Math.PI) / 180;
  cad.push(cad.mTrans(-4, 16, 36));
  cad.push(cad.mRotX(gRad));
  cad.extrudePoly(cad.gear2D(12, 11, 16), {
    origin: [0, 0, 0], uAxis: [0, 1, 0], vAxis: [0, 0, 1], wAxis: [1, 0, 0], depth: 11, tone: 'hi', key: 'step',
  });
  cad.pop(); cad.pop();

  // Driven Flywheel Ring Gear Coupling to High-Pressure Fuel Rail Pump
  cad.push(cad.mTrans(2, -26, 38));
  cad.push(cad.mRotX(-gRad * 0.55));
  cad.extrudePoly(cad.gear2D(20, 24, 29), {
    origin: [0, 0, 0], uAxis: [0, 1, 0], vAxis: [0, 0, 1], wAxis: [1, 0, 0], depth: 9, tone: 'body', key: 'step',
  });
  cad.pop(); cad.pop();

  // 4. Cylindrical Common Bytecode Fuel Rail + 4 Curved High-Pressure Lines + 4 Conical Injectors!
  // Cylindrical High-Pressure Accumulator Rail (z = 84)
  cad.cyl([18, -22, 84], [148, -22, 84], 8.5, 8.5, { segs: 20, tone: st.running ? 'hi' : 'dark', liveStroke: st.running });
  // Pump riser pipe feeding common rail
  cad.sweepTube([[11, -26, 56], [11, -22, 84], [22, -22, 84]], 3.2, { cornerR: 8, tone: 'hi' });

  // Cast Intake Runner Tube below the 4 injectors
  cad.cyl([24, 4, 18], [146, 4, 18], 14, 14, { segs: 20, tone: 'dark' });

  const injKeys = ['i0', 'i1', 'i2', 'step'];
  for (let i = 0; i < 4; i++) {
    const ix = 38 + i * 32;
    const firing = st.running && st.pc === i;
    // Curved high-pressure steel fuel line arcing from Common Rail into Injector top!
    cad.sweepTube([[ix, -22, 84], [ix, -4, 80], [ix, 4, 66]], 2.2, { cornerR: 9, tone: firing ? 'hi' : 'body', liveStroke: firing, key: injKeys[i] });
    // Stepped Cylindrical/Conical Solenoid Fuel Injector Nozzle!
    cad.revolve(
      [[26, 3.2], [34, 6.5], [46, 10.5], [62, 10.5], [66, 5.5]],
      { axis: 'z', origin: [ix, 4, 0], segs: 18, tone: firing ? 'hi' : 'body', liveStroke: firing, key: injKeys[i] }
    );
  }

  // Callouts
  cad.callout([-84, 16, 89], -42, -28, st.running ? '24V CRANKED' : 'CRANK 24V', { key: 'crank', op: st.running, sel: st.running });
  cad.callout([38 + st.pc * 32, 12, 54], 34, 42, 'STEP (' + OPS[st.pc].name + ')', { key: 'step', op: true });
  cad.callout([38, 12, 34], -36, 52, '1: LdaSmi', { key: 'i0', sel: st.running && st.pc === 0 });
  cad.callout([70, 12, 34],  4, 64, '2: Add', { key: 'i1', sel: st.running && st.pc === 1 });
  cad.callout([138, -22, 92], 36, -28, st.running ? 'CUT IGNITION' : 'IGNITION OFF', { key: 'cut', sel: !st.running });

  if (!st.running) return 'ignition off · 0 kPa · baseline required';
  return '24v on · inj #' + (st.pc + 1) + ' ' + OPS[st.pc].name + ' · acc ' + st.acc + ' · warm ' + st.warm;
}
`,
  });

  // ==========================================================================
  // FIG 6: Torque & CSA — Coiled-Steel Reel + 4-Column Tie-Rod Hydraulic Press
  // ==========================================================================
  writeCadFigure({
    slug: "fig-06-torque-csa",
    fig: "Fig 6",
    title: "Torque & CSA · Uncoiler Reel & 4-Column Tie-Rod Press",
    hint: "strike hydraulic ram · switch .tq target · drag to orbit",
    initialReadout: "station 4/4 · ArrayPrototypePush · 3 built-ins",
    ariaLabel:
      "3D isometric progressive stamping line for V8 Torque and CodeStubAssembler, featuring a large cylindrical coiled-steel uncoiler reel feeding an S-curved metal strip through four chrome tie-rod guide pillars with helical return springs beneath an arched hydraulic press crown.",
    footHelp:
      "Click parts or keys: <kbd>Space</kbd> / <kbd>S</kbd> strike progressive ram · <kbd>T</kbd> switch <code>.tq</code> built-in target · <kbd>R</kbd> reset coil strip · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 38,
    elDeg: 27,
    sceneJs: `
const TARGETS = ['ArrayPrototypePush', 'LoadIC_BytecodeHandler', 'StringAdd_CheckNone', 'FastNewObjectStub'];
const st = { step: 4, targetIdx: 0, stamped: 3, ramDrop: 0, reelDeg: 0 };
const KM = { ' ': 'strike', Enter: 'strike', s: 'strike', t: 'spec', r: 'rst', Escape: 'rst' };

function act(k) {
  if (k === 'strike') {
    if (st.step < 4) st.step++;
    else { st.stamped++; st.step = 1; st.targetIdx = (st.targetIdx + 1) % TARGETS.length; }
    st.reelDeg = (st.reelDeg + 32) % 360;
    st.ramDrop = 14;
    redraw(false);
    setTimeout(() => { st.ramDrop = 0; redraw(false); }, 150);
    return;
  } else if (k === 'spec') {
    st.targetIdx = (st.targetIdx + 1) % TARGETS.length;
    st.step = 1;
  } else if (k === 'rst') {
    st.step = 0;
  }
  redraw(false);
}

function buildScene(cad) {
  // 1. Left Giant Cylindrical Sheet-Metal Coil Unwinder Reel on A-Frame Mandrel!
  for (const sy of [-22, 22]) {
    cad.sweepTube([[-146, sy, 0], [-128, sy * 0.7, 56], [-110, sy, 0]], 3.0, { cornerR: 6, tone: 'dark' });
  }
  // Wound Steel Strip Coil Cylinder + Expanding Mandrel Spokes
  cad.cyl([-128, -15, 56], [-128, 15, 56], 38, 38, { segs: 28, holeR: 13, ribEvery: 3, tone: 'hi', key: 'spec' });
  const rRad = (st.reelDeg * Math.PI) / 180;
  for (let s = 0; s < 4; s++) {
    const a = rRad + (s * Math.PI) / 2;
    cad.sweepTube([[-128, 16, 56], [-128 + Math.cos(a) * 28, 17, 56 + Math.sin(a) * 28]], 2.0, { tone: 'body', key: 'spec' });
  }

  // 2. S-Curved Continuous Steel Strip Ribbon feeding from Uncoiler through the 4 Die Stations!
  const stripPath = [[-102, 0, 74], [-78, 0, 52], [-52, 0, 38], [116, 0, 38], [142, 0, 28]];
  cad.sweepTube(stripPath, 3.2, { cornerR: 16, tone: 'hi' });

  // 3. Cast Press Lower Bolster on 4 Cylindrical Feet (x = -46 .. +124)
  for (const [fx, fy] of [[-38,-34],[116,-34],[-38,34],[116,34]]) {
    cad.cyl([fx, fy, 0], [fx, fy, 16], 9, 8, { segs: 14, tone: 'dark' });
  }
  cad.box3(-48, -42, 16, 174, 84, 16, { tone: 'dark' });

  // 4. Four Tall Cylindrical Chrome Guide Tie-Rods + Coaxial Helical Return Springs!
  for (const [px, py] of [[-36, -32], [114, -32], [-36, 32], [114, 32]]) {
    cad.cyl([px, py, 32], [px, py, 134], 5.5, 5.5, { segs: 16, tone: 'hi' });
    // Helical return spring around lower half of each tie-rod!
    cad.sweepTube(cad.helix3D(px, py, 8.2, 8.2, 34, 78 - st.ramDrop * 0.5, 3.5, 24), 1.3, { segs: 8, tone: 'body' });
    // Top hex locknuts above crown
    cad.cyl([px, py, 134], [px, py, 142], 8.5, 8.5, { segs: 6, tone: 'hi' });
  }

  // 5. Four Hardened Progressive Die Stations along the Strip (S1 .tq -> S2 CSA -> S3 Graph -> S4 Blob)
  for (let i = 0; i < 4; i++) {
    const sx = -14 + i * 34;
    const stamped = i < st.step;
    cad.cyl([sx, 0, 32], [sx, 0, 42], 13, 11, {
      segs: 16,
      tone: stamped ? 'hi' : 'body',
      liveStroke: stamped,
      key: 'strike',
    });
    // Descending upper punch tool attached to moving ram platen
    cad.cyl([sx, 0, 68 - st.ramDrop], [sx, 0, 84 - st.ramDrop], 8.5, 10, {
      segs: 16,
      tone: stamped ? 'hi' : 'dark',
      key: 'strike',
    });
  }

  // 6. Moving Upper Ram Platen + Arched Cast Crown Entablature + Massive Central Hydraulic Cylinder!
  cad.box3(-44, -38, 84 - st.ramDrop, 166, 76, 14, { tone: 'body', key: 'strike' });
  // Arched Crown Entablature spanning top of the 4 tie-rods (z = 114..134)
  cad.extrudePoly(
    [[-46, 114], [124, 114], [124, 126], [68, 138], [10, 138], [-46, 126]],
    { origin: [0, -38, 0], uAxis: [1, 0, 0], vAxis: [0, 0, 1], wAxis: [0, 1, 0], depth: 76, tone: 'body' }
  );
  // Central Main Hydraulic Cylinder + Piston Rod + Curved Hydraulic Supply Pipes!
  cad.revolve(
    [[138, 26], [172, 26], [178, 20], [182, 0.5]],
    { axis: 'z', origin: [39, 0, 0], segs: 24, ribRings: [0, 1], tone: 'hi', key: 'strike' }
  );
  cad.cyl([39, 0, 98 - st.ramDrop], [39, 0, 116], 13, 13, { segs: 18, tone: 'hi' });
  cad.sweepTube([[14, 0, 166], [-8, -28, 156], [-8, -28, 126]], 2.6, { cornerR: 10, tone: 'hi' });

  // Callouts
  cad.callout([39, 0, 174], 38, -24, 'STRIKE DIE [' + st.step + '/4]', { key: 'strike', op: true });
  cad.callout([-128, 18, 88], -36, -28, 'TARGET: ' + TARGETS[st.targetIdx], { key: 'spec', sel: true });
  cad.callout([96, 36, 26], 36, 36, 'RESET COIL', { key: 'rst' });

  return 'station ' + st.step + '/4 · ' + TARGETS[st.targetIdx] + ' · ' + st.stamped + ' built-ins';
}
`,
  });

  // ==========================================================================
  // FIG 7: Orinoco Old Space — Open-Lattice Rack & Tapered Laser Stacker Crane
  // ==========================================================================
  writeCadFigure({
    slug: "fig-07-old-space",
    fig: "Fig 7",
    title: "Orinoco Old Space · Lattice Rack & Laser Stacker Crane",
    hint: "laser-mark drums · sweep white bays · compact shelves · drag to orbit",
    initialReadout: "ready · 6 live / 3 dead · 25% frag",
    ariaLabel:
      "3D isometric open-lattice high-bay AS/RS warehouse rack holding cylindrical Old-Space memory drums across 3 tiers, served by a traveling twin-mast tapered stacker crane with a vertical laser inventory shuttle.",
    footHelp:
      "Click parts or keys: <kbd>A</kbd> store Old-Space drum · <kbd>U</kbd> orphan a drum (unroot) · <kbd>L</kbd> / <kbd>M</kbd> laser tricolor mark · <kbd>S</kbd> sweep white drums · <kbd>C</kbd> / <kbd>Space</kbd> compact rack · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 38,
    elDeg: 26,
    sceneJs: `
const st = {
  bays: [
    { root: true, marked: true }, null, { root: false, marked: false }, { root: true, marked: true },
    { root: true, marked: true }, { root: false, marked: false }, { root: true, marked: true }, null,
    { root: false, marked: false }, { root: true, marked: true }, null, { root: true, marked: true },
  ],
  craneCol: 1,
  craneTier: 1,
  phase: 'ready',
};
const KM = { a: 'alloc', u: 'drop', l: 'mark', m: 'mark', s: 'sweep', c: 'compact', ' ': 'compact' };

function act(k) {
  if (k === 'alloc') {
    const idx = st.bays.findIndex((b) => b === null);
    if (idx >= 0) {
      st.bays[idx] = { root: true, marked: false };
      st.craneCol = idx % 4; st.craneTier = Math.floor(idx / 4);
      st.phase = 'stored #' + idx;
    } else st.phase = 'rack full';
  } else if (k === 'drop') {
    const idx = st.bays.findIndex((b) => b && b.root);
    if (idx >= 0) {
      st.bays[idx].root = false; st.bays[idx].marked = false;
      st.craneCol = idx % 4; st.craneTier = Math.floor(idx / 4);
      st.phase = 'unrooted #' + idx;
    }
  } else if (k === 'mark') {
    st.bays.forEach((b) => { if (b) b.marked = b.root; });
    st.craneCol = (st.craneCol + 1) % 4;
    st.craneTier = (st.craneTier + 1) % 3;
    st.phase = 'laser marked';
  } else if (k === 'sweep') {
    let freed = 0;
    st.bays = st.bays.map((b) => {
      if (b && !b.root) { freed++; return null; }
      return b;
    });
    st.craneCol = 2; st.craneTier = 0;
    st.phase = 'swept ' + freed;
  } else if (k === 'compact') {
    const survivors = st.bays.filter((b) => b && b.root).map(() => ({ root: true, marked: true }));
    while (survivors.length < 12) survivors.push(null);
    st.bays = survivors;
    st.craneCol = Math.max(0, (survivors.filter(Boolean).length - 1) % 4);
    st.craneTier = 0;
    st.phase = 'compacted';
  }
  redraw(false);
}

function buildScene(cad) {
  // 1. Tall Open-Lattice Tubular 4-Column × 3-Tier High-Bay Storage Rack (NO floor slab, NO black box!)
  for (let c = 0; c <= 4; c++) {
    const ux = -104 + c * 52;
    cad.cyl([ux, -34, 0], [ux, -34, 168], 2.8, 2.8, { segs: 10, tone: 'dark' });
    cad.cyl([ux,   6, 0], [ux,   6, 168], 2.8, 2.8, { segs: 10, tone: 'body' });
    // Diagonal X-bracing up the side frames!
    for (let t = 0; t < 3; t++) {
      const z0 = 8 + t * 52, z1 = z0 + 50;
      cad.sweepTube([[ux, -34, z0], [ux, 6, z1]], 1.2, { tone: 'dark' });
      cad.sweepTube([[ux, 6, z0], [ux, -34, z1]], 1.2, { tone: 'dark' });
    }
  }
  // Tubular Shelf Beams for the 3 Tiers + Roof Tie
  for (let t = 0; t <= 3; t++) {
    const sz = 10 + t * 52;
    cad.cyl([-106, -34, sz], [106, -34, sz], 2.4, 2.4, { segs: 10, tone: 'body' });
    cad.cyl([-106,   6, sz], [106,   6, sz], 2.4, 2.4, { segs: 10, tone: 'body' });
  }

  // 2. Cylindrical Memory Capsule Drums stored in the 12 Rack Bays (Black/Live = bright ribbed, White = dull!)
  let live = 0, dead = 0, holes = 0, lastUsed = -1;
  st.bays.forEach((b, idx) => {
    if (!b) return;
    lastUsed = idx;
    if (b.root) live++; else dead++;
    const col = idx % 4, tier = Math.floor(idx / 4);
    const bx = -78 + col * 52, by = -14, bz = 13 + tier * 52;
    const isBlack = b.root && b.marked;
    // Vertical flanged memory capsule cylinder!
    cad.revolve(
      [[0, 15], [5, 16], [30, 16], [36, 11], [38, 0.4]],
      {
        axis: 'z',
        origin: [bx, by, bz],
        segs: 18,
        ribRings: [1, 2],
        tone: isBlack ? 'hi' : (b.root ? 'body' : 'dark'),
        liveStroke: isBlack,
        key: b.root ? 'drop' : 'sweep',
      }
    );
  });
  for (let i = 0; i < lastUsed; i++) if (!st.bays[i]) holes++;
  const frag = lastUsed >= 0 ? Math.round((holes / (lastUsed + 1)) * 100) : 0;

  // 3. Twin Tubular Floor & Overhead Crane Guide Rails + Tapered Twin-Mast Stacker Crane!
  cad.cyl([-114, 34, 4], [114, 34, 4], 3.0, 3.0, { segs: 12, tone: 'body' });
  cad.cyl([-114, 52, 4], [114, 52, 4], 3.0, 3.0, { segs: 12, tone: 'body' });

  const cx = -78 + st.craneCol * 52;
  const sz = 22 + st.craneTier * 52;
  // Bogie wheel carriage on twin rails
  cad.box3(cx - 18, 30, 6, 36, 26, 8, { tone: 'hi', key: 'mark' });
  for (const wx of [cx - 13, cx + 13]) {
    cad.cyl([wx, 31, 5], [wx, 37, 5], 4.5, 4.5, { segs: 12, tone: 'hi' });
    cad.cyl([wx, 49, 5], [wx, 55, 5], 4.5, 4.5, { segs: 12, tone: 'hi' });
  }
  // Tall Tapered Twin-Tube Mast rising to z = 182!
  cad.cyl([cx - 9, 43, 14], [cx - 4, 43, 180], 3.0, 2.0, { segs: 12, tone: 'hi', key: 'mark' });
  cad.cyl([cx + 9, 43, 14], [cx + 4, 43, 180], 3.0, 2.0, { segs: 12, tone: 'hi', key: 'mark' });
  for (let r = 0; r < 6; r++) {
    const rz = 32 + r * 24;
    cad.sweepTube([[cx - 8, 43, rz], [cx + 8, 43, rz + 12]], 1.2, { tone: 'body' });
  }
  // Elevating Fork & Rotary Laser Scanner Turret + Twin Laser Scan Beams into the target bay!
  cad.cyl([cx, 40, sz], [cx, 18, sz], 9.5, 6.5, { segs: 16, tone: 'hi', liveStroke: true, key: 'mark' });
  cad.sweepTube([[cx, 18, sz + 2], [cx - 9, -8, sz + 12]], 0.9, { tone: 'hi', liveStroke: true });
  cad.sweepTube([[cx, 18, sz - 2], [cx + 9, -8, sz - 4]], 0.9, { tone: 'hi', liveStroke: true });

  // Callouts
  cad.callout([cx, 43, 180], 38, -20, 'LASER MARK', { key: 'mark', op: true });
  cad.callout([-98, 6, 152], -44, -22, '+STORE DRUM', { key: 'alloc' });
  cad.callout([-98, 6, 92], -46, 14, 'UNROOT DRUM', { key: 'drop' });
  cad.callout([98, 6, 118], 42, -12, 'SWEEP WHITE (' + dead + ')', { key: 'sweep', sel: dead > 0 });
  cad.callout([98, 48, 12], 36, 36, 'COMPACT (' + frag + '% FRAG)', { key: 'compact', op: frag > 0 });

  return st.phase + ' · ' + live + ' live / ' + dead + ' dead · ' + frag + '% frag';
}
`,
  });

  // ==========================================================================
  // FIG 8: Orinoco New Space — Stadium-Belt Eddy-Current Drum & Screw Auger
  // ==========================================================================
  writeCadFigure({
    slug: "fig-08-new-space",
    fig: "Fig 8",
    title: "Orinoco New Space · Stadium-Belt Eddy Rotor & Auger",
    hint: "feed nursery belt · pulse eddy drum · promote via auger · drag to orbit",
    initialReadout: "scavenger · 2 to-space / 4 dropped · 1 promoted",
    ariaLabel:
      "3D isometric dual-belt eddy-current chip separator for V8 Orinoco New Space Scavenger, with rounded stadium conveyor loop around cylindrical pulleys on an angled steel trestle, spinning ribbed magnetic eddy-current drum, conical dead-chip drop hopper, lower To-Space stadium belt, and vertical helical screw-auger promotion elevator.",
    footHelp:
      "Click parts or keys: <kbd>F</kbd> feed Nursery chips · <kbd>D</kbd> die young · <kbd>Space</kbd> / <kbd>S</kbd> scavenge pulse · <kbd>P</kbd> promote via screw auger · <kbd>Esc</kbd> clear · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 37,
    elDeg: 27,
    sceneJs: `
const st = {
  nursery: [{ live: true }, { live: false }, { live: true }],
  toSpace: [{ age: 1 }, { age: 2 }],
  dropped: 4,
  promoted: 1,
  rotorDeg: 0,
};
const KM = { f: 'feed', d: 'die', s: 'scav', ' ': 'scav', Enter: 'scav', p: 'promo', Escape: 'rst' };

function act(k) {
  if (k === 'feed') {
    st.nursery = [{ live: true }, { live: false }, { live: st.dropped % 2 === 0 }];
  } else if (k === 'die') {
    st.nursery.forEach((c, idx) => { if (c && idx > 0) c.live = false; });
  } else if (k === 'scav') {
    st.rotorDeg = (st.rotorDeg + 37) % 360;
    const survivors = [];
    st.nursery.forEach((c) => {
      if (!c) return;
      if (c.live) survivors.push({ age: 1 });
      else st.dropped++;
    });
    st.nursery = [null, null, null];
    st.toSpace = [...st.toSpace.map((s) => ({ age: s.age + 1 })), ...survivors];
    while (st.toSpace.length > 2) {
      st.toSpace.shift();
      st.promoted++;
    }
  } else if (k === 'promo') {
    st.rotorDeg = (st.rotorDeg + 25) % 360;
    const kept = [];
    st.toSpace.forEach((s) => {
      if (s.age >= 2 || kept.length >= 1) st.promoted++;
      else kept.push({ age: s.age + 1 });
    });
    st.toSpace = kept;
  } else if (k === 'rst') {
    st.nursery = [{ live: true }, { live: false }, { live: false }];
    st.toSpace = [];
    st.dropped = 0;
    st.promoted = 0;
  }
  redraw(false);
}

function buildScene(cad) {
  // 1. Angled Open A-Frame Trestle supporting Upper From-Space Stadium Conveyor Belt!
  for (const sy of [-22, 22]) {
    cad.sweepTube([[-138, sy, 0], [-122, sy, 76]], 2.8, { tone: 'dark' });
    cad.sweepTube([[-32,  sy, 0], [-22,  sy, 76]], 2.8, { tone: 'dark' });
    cad.sweepTube([[-130, sy, 36], [-26, sy, 36]], 1.8, { tone: 'dark' });
  }

  // Upper Rounded Stadium-Loop Conveyor Belt + Tail Pulley + Large Magnetic Eddy-Current Head Drum!
  cad.extrudePoly(cad.stadium2D(102, 16, 14), {
    origin: [-72, -20, 80],
    uAxis: [1, 0, 0],
    vAxis: [0, 0, 1],
    wAxis: [0, 1, 0],
    depth: 40,
    tone: 'body',
    key: 'feed',
  });
  // Tail idler pulley cylinder
  cad.cyl([-123, -23, 80], [-123, 23, 80], 13, 13, { segs: 18, tone: 'hi' });
  // Spinning High-Frequency Magnetic Eddy-Current Rotor Drum at discharge head (x = -21, z = 80)!
  cad.cyl([-21, -25, 80], [-21, 25, 80], 17.5, 17.5, { segs: 24, ribEvery: 2, tone: 'hi', liveStroke: true, key: 'scav' });

  // 3 Nursery Chip Allocations riding along the top run of the Upper Stadium Belt!
  for (let i = 0; i < 3; i++) {
    const c = st.nursery[i];
    if (!c) continue;
    const nx = -112 + i * 32;
    cad.cyl([nx, 0, 96], [nx, 0, 104], 10, 8.5, {
      segs: 8,
      tone: c.live ? 'hi' : 'dark',
      liveStroke: c.live,
      key: 'die',
    });
  }

  // 2. Zero-Cost Conical Dead-Chip Gravity Drop Funnel directly beneath Drum + Ballistic Arcs!
  cad.revolve(
    [[4, 7], [28, 25], [46, 28]],
    { axis: 'z', origin: [-10, 0, 0], segs: 22, doubleSided: true, ribRings: [1], tone: 'dark', key: 'scav' }
  );
  // Splitter Knife Blade separating dead vertical fall from repelled parabolic live-chip leap!
  cad.box3(16, -22, 34, 3, 44, 28, { tone: 'hi' });
  // Parabolic Repulsion Trajectory Arc over the Splitter Knife!
  cad.sweepTube([[-10, 0, 96], [16, 0, 98], [38, 0, 72], [54, 0, 38]], 1.4, { cornerR: 18, tone: 'hi', liveStroke: true });

  // 3. Lower To-Space Stadium Conveyor Belt (x = 28..108, z = 24)
  cad.extrudePoly(cad.stadium2D(68, 11, 12), {
    origin: [66, -18, 24],
    uAxis: [1, 0, 0],
    vAxis: [0, 0, 1],
    wAxis: [0, 1, 0],
    depth: 36,
    tone: 'body',
    key: 'scav',
  });
  for (let i = 0; i < 2; i++) {
    const s = st.toSpace[i];
    if (!s) continue;
    const sx = 48 + i * 30;
    cad.cyl([sx, 0, 35], [sx, 0, 44], 10.5, 9, { segs: 8, tone: 'hi', liveStroke: true, key: 'promo' });
  }

  // 4. Tall Vertical Cylindrical Helical Screw-Auger Promotion Elevator to Old Space (x = 126)!
  // Cutaway cylindrical auger casing so the internal climbing helical screw flight is visible!
  cad.revolve(
    [[0, 19], [116, 19]],
    { axis: 'z', origin: [126, 0, 0], segs: 22, a0: 0.75, a1: Math.PI * 1.65, doubleSided: true, tone: 'body', key: 'promo' }
  );
  cad.cyl([126, 0, 0], [126, 0, 124], 4.5, 4.5, { segs: 14, tone: 'hi', key: 'promo' });
  cad.sweepTube(cad.helix3D(126, 0, 14, 14, 10, 114, 4.2, 48), 2.4, { segs: 8, tone: 'hi', liveStroke: true, key: 'promo' });
  // Top discharge spout to Old Space
  cad.sweepTube([[126, 0, 112], [148, -14, 104]], 5.5, { tone: 'hi', key: 'promo' });

  // Callouts
  cad.callout([-96, 16, 98], -42, -32, 'FEED NURSERY', { key: 'feed' });
  cad.callout([-58, -18, 96], -44, 34, 'DIE YOUNG', { key: 'die' });
  cad.callout([-21, 22, 92], 14, -44, 'SCAVENGE PULSE', { key: 'scav', op: true });
  cad.callout([-10, 24, 24], -26, 48, st.dropped + ' DROPPED (0 CYC)', { key: 'scav' });
  cad.callout([126, 16, 118], 38, -24, 'AUGER PROMOTE (' + st.promoted + ')', { key: 'promo', op: true });

  return 'scavenger · ' + st.toSpace.length + ' to-space / ' + st.dropped + ' dropped · ' + st.promoted + ' promoted';
}
`,
  });
}
