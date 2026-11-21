import { writeCadFigure } from "./iso-cad.mjs";

export function buildFigs1To4() {
  // ==========================================================================
  // FIG 1: v8::Isolate — Twin Domed Pressure-Silo Skid & Centrifugal Pump
  // ==========================================================================
  writeCadFigure({
    slug: "fig-01-isolate",
    fig: "Fig 1",
    title: "v8::Isolate · Twin-Silo Process Skid",
    hint: "lock thread cam · spawn realm silo · drain pump · drag to orbit",
    initialReadout: "thread #1 locked · 1 realm · 2 tasks",
    ariaLabel:
      "3D isometric v8::Isolate refinery-style process skid on open structural steel I-beams, featuring two vertical cylindrical domed heap silos, overhead flanged manifold piping, a centrifugal microtask volute pump, tubular cage handrails, and a rotary v8::Locker cam switch.",
    footHelp:
      "Click parts or keys: <kbd>1</kbd> lock Thread #1 · <kbd>2</kbd> contend Thread #2 · <kbd>U</kbd> unlock v8::Locker · <kbd>R</kbd> spawn Context/Realm · <kbd>M</kbd> enqueue microtask · <kbd>D</kbd> drain pump · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 40,
    elDeg: 28,
    sceneJs: `
const st = { owner: 1, realms: 1, tasks: 2, blocked: false };
const KM = { '1': 't1', '2': 't2', u: 'unlock', r: 'realm', m: 'enq', d: 'drain', ' ': 'drain' };

function act(k) {
  st.blocked = false;
  if (k === 't1' || k === 't2') {
    const want = k === 't1' ? 1 : 2;
    if (st.owner !== 0 && st.owner !== want) st.blocked = true;
    else st.owner = want;
  } else if (k === 'unlock') {
    st.owner = 0;
  } else if (k === 'realm') {
    if (!st.owner) st.blocked = true;
    else st.realms = (st.realms % 4) + 1;
  } else if (k === 'enq') {
    if (!st.owner) st.blocked = true;
    else if (st.tasks < 4) st.tasks++;
  } else if (k === 'drain') {
    if (!st.owner) st.blocked = true;
    else st.tasks = 0;
  }
  redraw(false);
}

function buildScene(cad) {
  // 1. Open Structural Steel I-Beam Skid Rails (NO flat rectangular slab!)
  const iBeam2D = [[-8,0],[8,0],[8,3],[2.2,3],[2.2,13],[8,13],[8,16],[-8,16],[-8,13],[-2.2,13],[-2.2,3],[-8,3]];
  for (const ry of [-56, 56]) {
    cad.extrudePoly(iBeam2D, { origin: [-118, ry, 0], uAxis: [0, 1, 0], vAxis: [0, 0, 1], wAxis: [1, 0, 0], depth: 236, tone: 'dark' });
  }
  // 4 Transverse Structural Cross-Channels
  for (const cx of [-96, -28, 42, 102]) {
    cad.box3(cx - 4, -50, 4, 8, 100, 9, { tone: 'dark' });
  }

  // 2. Tubular Yellow/Accent 4 GiB Pointer-Compression Cage Safety Handrails (swept 3D pipes!)
  cad.sweepTube([[-112, -58, 16], [-112, -58, 66], [112, -58, 66], [112, -58, 16]], 2.1, { cornerR: 8, tone: 'body' });
  cad.sweepTube([[-112, -58, 66], [-112, 58, 66], [-48, 58, 66]], 2.1, { cornerR: 8, tone: 'body' });

  // 3. Tall Cylindrical Domed 4 GiB Cage Heap Silo (left-rear, lathed pressure vessel!)
  for (const ang of [0.6, 2.2, 3.8, 5.4]) {
    cad.cyl([-56 + Math.cos(ang)*26, -16 + Math.sin(ang)*26, 14], [-56 + Math.cos(ang)*26, -16 + Math.sin(ang)*26, 36], 2.6, 2.6, { segs: 10, tone: 'dark' });
  }
  cad.revolve(
    [[30, 0.4], [33, 18], [40, 31], [118, 31], [128, 25], [135, 13], [138, 0.4]],
    { axis: 'z', origin: [-56, -16, 0], segs: 26, ribRings: [2, 3], tone: 'body' }
  );
  // Top Flanged Manway Neck on Main Silo
  cad.cyl([-56, -16, 137], [-56, -16, 147], 8, 8, { segs: 16, tone: 'hi' });
  cad.cyl([-56, -16, 147], [-56, -16, 150], 11.5, 11.5, { segs: 16, tone: 'hi' });

  // 4. Secondary Cylindrical Context / Realm Silo (scales ring bands with st.realms!)
  cad.revolve(
    [[26, 0.4], [30, 16], [36, 25], [96 + st.realms * 7, 25], [105 + st.realms * 7, 17], [110 + st.realms * 7, 0.4]],
    { axis: 'z', origin: [18, -22, 0], segs: 24, ribRings: [2, 3], tone: 'hi', key: 'realm' }
  );
  // Realm Sight-Rings wrapped around Secondary Silo
  for (let r = 0; r < st.realms; r++) {
    cad.cyl([18, -22, 44 + r * 14], [18, -22, 48 + r * 14], 26.8, 26.8, { segs: 22, tone: 'hi', liveStroke: true, key: 'realm' });
  }

  // 5. Overhead Swept 3D Process Manifold Pipes & Valve Flanges connecting Silos -> Pump!
  cad.sweepTube([[-56, -16, 144], [-56, -16, 162], [18, -22, 162], [18, -22, 108 + st.realms * 7]], 4.2, { cornerR: 14, tone: 'hi' });
  cad.sweepTube([[18, -2, 54], [58, -2, 54], [76, 18, 36]], 4.0, { cornerR: 12, tone: 'body' });

  // 6. Centrifugal Microtask Volute Pump & 4 Illuminated Ring Stages (front-right!)
  cad.cyl([76, 22, 16], [76, 22, 24], 22, 20, { segs: 20, tone: 'dark' }); // pump pedestal
  cad.cyl([76, 10, 42], [76, 36, 42], 21, 21, { segs: 24, holeR: 9, tone: st.tasks > 0 ? 'hi' : 'body', key: 'drain' });
  // Tangential vertical discharge stack with 4 microtask sight rings!
  cad.cyl([91, 22, 42], [91, 22, 96], 6.5, 6.5, { segs: 16, tone: 'body', key: 'enq' });
  for (let q = 0; q < 4; q++) {
    const active = q < st.tasks;
    cad.cyl([91, 22, 52 + q * 10], [91, 22, 57 + q * 10], active ? 9.2 : 7.4, active ? 9.2 : 7.4, {
      segs: 16,
      tone: active ? 'hi' : 'dark',
      liveStroke: active,
      key: 'enq',
    });
  }

  // 7. Front-Left Rotary v8::Locker Cam Valve & Handwheel (rotates between T1, Idle, Contended T2!)
  cad.cyl([-52, 36, 16], [-52, 36, 52], 12, 10, { segs: 18, tone: 'body', key: 't1' });
  const wheelAngle = st.owner === 1 ? -0.55 : st.owner === 2 ? 0.55 : 0;
  cad.push(cad.mTrans(-52, 46, 44));
  cad.push(cad.mRotY(wheelAngle));
  // Toroidal/hollow handwheel rim + 3 spokes + locking lever handle
  cad.cyl([0, 0, 0], [0, 5, 0], 19, 19, { segs: 22, holeR: 15, tone: st.owner ? 'hi' : 'body', liveStroke: st.blocked, key: 't2' });
  for (let s = 0; s < 3; s++) {
    const a = (s * Math.PI * 2) / 3;
    cad.sweepTube([[0, 2.5, 0], [Math.cos(a) * 16, 2.5, Math.sin(a) * 16]], 1.8, { tone: 'hi', key: 't2' });
  }
  cad.cyl([0, 5, 16], [0, 14, 16], 2.5, 2.5, { segs: 10, tone: 'hi', key: 'unlock' });
  cad.pop(); cad.pop();

  // Direct Technical Callouts
  cad.callout([-52, 54, 56], -44, 34, st.owner === 1 ? 'LOCKED: T1' : 'LOCK T1', { key: 't1', op: st.owner === 1, sel: st.owner === 1 });
  cad.callout([-36, 50, 32], -26, 62, st.blocked ? 'DENIED: T2 CONTENDED' : (st.owner === 2 ? 'LOCKED: T2' : 'TRY THREAD #2'), { key: 't2', sel: st.blocked || st.owner === 2 });
  cad.callout([-68, 36, 24], -54, -18, st.owner === 0 ? 'IDLE (UNLOCKED)' : 'UNLOCK LOCKER', { key: 'unlock', sel: st.owner === 0 });
  cad.callout([18, -22, 112 + st.realms * 7], 36, -28, '+REALM (' + st.realms + ')', { key: 'realm', op: true });
  cad.callout([91, 22, 96], 42, -20, '+TASK (' + st.tasks + '/4)', { key: 'enq' });
  cad.callout([76, 36, 40], 40, 38, 'DRAIN PUMP', { key: 'drain', op: true });

  const lockStr = st.owner ? 'thread #' + st.owner + ' locked' : 'unlocked';
  return (st.blocked ? 'contended · ' : '') + lockStr + ' · ' + st.realms + (st.realms === 1 ? ' realm · ' : ' realms · ') + st.tasks + ' tasks';
}
`,
  });

  // ==========================================================================
  // FIG 2: Pointer Tagging — Parabolic Bit-0 Laser Arch & Carousel Vault
  // ==========================================================================
  writeCadFigure({
    slug: "fig-02-pointer-tagging",
    fig: "Fig 2",
    title: "Pointer Tagging · Roller Bridge & RFID Carousel",
    hint: "stamp forged smi gear · switch to rfid + heap carousel · drag to orbit",
    initialReadout: "smi · 0x00000054 (bit0=0) · val 42 · 0 derefs",
    ariaLabel:
      "3D isometric pointer-tagging inspection bridge with 14 cylindrical steel rollers on open angled trestle legs, a parabolic tubular bit-0 laser scanner arch, switching between a forged 8-tooth metal gear casting (Smi bit0=0) and a thin RFID manifest linked to a rotating 6-pod cylindrical HeapObject carousel.",
    footHelp:
      "Click parts or keys: <kbd>S</kbd> forged Smi casting (<kbd>bit0=0</kbd>) · <kbd>D</kbd> shift Smi ×2 · <kbd>H</kbd> / <kbd>Space</kbd> RFID HeapObject wafer (<kbd>bit0=1</kbd>) · <kbd>F</kbd> mutate heap pod · <kbd>N</kbd> index roller bridge · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 35,
    elDeg: 27,
    sceneJs: `
const st = { isHeap: false, smiVal: 42, propVal: 108, slotOffset: 0 };
const KM = { s: 'smi', d: 'shl', h: 'heap', ' ': 'heap', f: 'field', n: 'next' };

function act(k) {
  if (k === 'smi') st.isHeap = false;
  else if (k === 'shl') { st.isHeap = false; st.smiVal = st.smiVal >= 512 ? 7 : st.smiVal * 2; }
  else if (k === 'heap') st.isHeap = true;
  else if (k === 'field') { st.isHeap = true; st.propVal += 12; }
  else if (k === 'next') { st.slotOffset = ((st.slotOffset + 2) % 3) - 1; }
  redraw(false);
}

function buildScene(cad) {
  // 1. Angled Open A-Frame Conveyor Trestle Legs + Twin Tubular Side Stringers (NO slab!)
  for (const lx of [-115, 0, 115]) {
    cad.sweepTube([[lx - 10, -36, 0], [lx, -28, 34]], 2.6, { tone: 'dark' });
    cad.sweepTube([[lx + 10,  36, 0], [lx,  28, 34]], 2.6, { tone: 'dark' });
    cad.sweepTube([[lx - 6, -32, 14], [lx + 6, 32, 14]], 1.8, { tone: 'dark' });
  }
  cad.cyl([-146, -30, 36], [146, -30, 36], 3.4, 3.4, { segs: 14, tone: 'body' });
  cad.cyl([-146,  30, 36], [146,  30, 36], 3.4, 3.4, { segs: 14, tone: 'body' });

  // 2. 15 True 3D Cylindrical Crowned Steel Conveyor Rollers!
  for (let i = 0; i < 15; i++) {
    const rx = -133 + i * 19;
    cad.cyl([rx, -28, 36], [rx, 28, 36], 5.2, 5.2, { segs: 14, tone: i % 2 === 0 ? 'hi' : 'body', key: 'next' });
  }

  // 3. Parabolic Tubular Bit-0 Laser Scanner Arch spanning the Conveyor Bridge!
  const archPts = [];
  for (let i = 0; i <= 18; i++) {
    const a = (Math.PI * i) / 18;
    archPts.push([-14, Math.cos(a) * 44, 36 + Math.sin(a) * 68]);
  }
  cad.sweepTube(archPts, 4.2, { segs: 14, tone: 'hi' });
  // Overhead Cylindrical Laser Scan Pod hanging from crown of arch
  cad.cyl([-14, 0, 102], [-14, 0, 86], 9, 6, { segs: 16, tone: 'hi', liveStroke: true });

  // 4. Carrier Payload in Laser Gate: Forged 10-Tooth Smi Gear Casting vs Wafer RFID Manifest!
  const cx = -14 + st.slotOffset * 26;
  // Open-frame carrier tray
  cad.box3(cx - 26, -22, 41.5, 52, 44, 3, { tone: 'body' });

  if (!st.isHeap) {
    // ON-CARRIER FORGED METAL GEAR & FLANGED HUB (31-bit immediate Smi, 0 heap derefs!)
    cad.extrudePoly(cad.gear2D(10, 15, 20), {
      origin: [cx, 0, 44.5],
      uAxis: [1, 0, 0],
      vAxis: [0, 1, 0],
      wAxis: [0, 0, 1],
      depth: 10,
      tone: 'hi',
      liveStroke: true,
      key: 'shl',
    });
    cad.revolve(
      [[54.5, 11], [64, 9], [68, 5], [68, 0.3]],
      { axis: 'z', origin: [cx, 0, 0], segs: 20, tone: 'hi', key: 'shl' }
    );
  } else {
    // FLAT WAFER RFID TRANSPONDER RING + FIBER-OPTIC DEREFERENCE BEAM TO REAR CAROUSEL!
    cad.cyl([cx, 0, 44.5], [cx, 0, 47.5], 18, 18, { segs: 22, holeR: 9, tone: 'hi', liveStroke: true, key: 'heap' });
    cad.cyl([cx, 0, 44.5], [cx, 0, 48.5], 5, 5, { segs: 14, tone: 'hi', key: 'heap' });
    // Swept luminous dereference conduit jumping from scanner arch to Rear Heap Carousel!
    cad.sweepTube([[-14, 0, 98], [18, -48, 112], [68, -88, 92]], 1.8, { cornerR: 22, tone: 'hi', liveStroke: true });
  }

  // 5. Off-Bridge Rotating 6-Pod Cylindrical HeapObject Carousel Vault (rear-right!)
  cad.cyl([68, -92, 0], [68, -92, 16], 34, 30, { segs: 22, tone: 'dark' }); // carousel pedestal
  cad.cyl([68, -92, 16], [68, -92, 90], 10, 8, { segs: 16, tone: 'body' }); // central spindle
  cad.cyl([68, -92, 16], [68, -92, 22], 38, 38, { segs: 24, tone: 'body', key: 'field' }); // rotary platter
  for (let p = 0; p < 6; p++) {
    const a = (p * Math.PI * 2) / 6 + st.propVal * 0.03;
    const px = 68 + Math.cos(a) * 24, py = -92 + Math.sin(a) * 24;
    const activePod = st.isHeap && p === 0;
    cad.cyl([px, py, 22], [px, py, activePod ? 76 : 62], 8.5, 8.5, {
      segs: 16,
      tone: activePod ? 'hi' : 'dark',
      liveStroke: activePod,
      key: 'field',
    });
  }

  // Callouts
  cad.callout([cx, 18, 56], -48, 44, 'SMI GEAR (bit0=0 · #' + st.smiVal + ')', { key: 'smi', op: !st.isHeap, sel: !st.isHeap });
  cad.callout([-14, 32, 84], -52, -26, 'SHIFT SMI ×2', { key: 'shl' });
  cad.callout([68, -92, 86], 36, -28, 'RFID -> HEAP (bit0=1)', { key: 'heap', op: st.isHeap, sel: st.isHeap });
  cad.callout([94, -84, 48], 42, 24, '+FIELD ({x:' + st.propVal + '})', { key: 'field', sel: st.isHeap });
  cad.callout([96, 28, 38], 34, 42, 'ADVANCE ROLLERS', { key: 'next' });

  if (!st.isHeap) {
    const raw = ((st.smiVal << 1) >>> 0).toString(16).padStart(8, '0');
    return 'smi · 0x' + raw + ' (bit0=0) · val ' + st.smiVal + ' · 0 derefs';
  }
  const hex = ((0x00184201 + st.slotOffset * 16) >>> 0).toString(16).padStart(8, '0');
  return 'heapobj · 0x' + hex + ' (bit0=1) · {x:' + st.propVal + '} · 1 deref';
}
`,
  });

  // ==========================================================================
  // FIG 3: Hidden Classes (Map) — Swan-Neck C-Frame Rotary Turret Punch Press
  // ==========================================================================
  writeCadFigure({
    slug: "fig-03-hidden-classes",
    fig: "Fig 3",
    title: "Hidden Classes · Swan-Neck C-Frame Turret Press",
    hint: "rotate die turret (+x/+y/+z) · test delete · drag to orbit",
    initialReadout: "map#2 {x@+4, y@+8} · die #2",
    ariaLabel:
      "3D isometric monolithic swan-neck C-frame rotary turret punch press for V8 HiddenClasses and Map transitions, with extruded curved cast-iron throat, rotating cylindrical upper and lower indexing discs carrying 4 round hardened punch dies, top hydraulic striker cylinder, and cantilevered X-Y sheet clamp.",
    footHelp:
      "Click dies or keys: <kbd>X</kbd> punch <code>+x (@+4)</code> · <kbd>Y</kbd> punch <code>+y (@+8)</code> · <kbd>Z</kbd> punch <code>+z (@+12)</code> · <kbd>D</kbd> delete property (degrades to dictionary mode) · <kbd>N</kbd> fresh JSObject blank · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 38,
    elDeg: 28,
    sceneJs: `
const st = { props: ['x', 'y'], dict: false, stroke: 0 };
const KM = { x: 'x', y: 'y', z: 'z', d: 'del', Backspace: 'del', n: 'new', Escape: 'new' };

function act(k) {
  if (k === 'new') { st.props = []; st.dict = false; }
  else if (k === 'del') { st.props.pop(); st.dict = true; }
  else if (['x', 'y', 'z'].includes(k)) {
    if (!st.props.includes(k) && st.props.length < 3) st.props.push(k);
  }
  st.stroke = 9;
  redraw(false);
  setTimeout(() => { st.stroke = 0; redraw(false); }, 150);
}

function buildScene(cad) {
  const n = st.props.length;

  // 1. Monolithic Cast-Iron Swan-Neck C-Frame Profile (concave extruded 2D casting!)
  const cFrame2D = [
    [-86, 0], [58, 0], [64, 18], [4, 22],
    [-26, 28], [-34, 48], [-34, 92], [-18, 106],
    [48, 108], [54, 124], [38, 146], [-68, 146],
    [-86, 126],
  ];
  cad.extrudePoly(cFrame2D, {
    origin: [0, -26, 0],
    uAxis: [1, 0, 0],
    vAxis: [0, 0, 1],
    wAxis: [0, 1, 0],
    depth: 52,
    tone: 'body',
  });
  // Cast side stiffening flange ribs along C-frame cheeks
  for (const sy of [-28, 26]) {
    cad.sweepTube([[-64, sy, 18], [-64, sy, 130], [28, sy, 130]], 2.4, { cornerR: 16, tone: 'dark' });
  }

  // 2. Top Hydraulic Striker Cylinder & Descending Ram Piston on Swan-Neck Nose!
  cad.revolve(
    [[146, 22], [176, 22], [182, 16], [186, 0.4]],
    { axis: 'z', origin: [26, 0, 0], segs: 22, ribRings: [0, 1], tone: 'hi' }
  );
  cad.cyl([26, 0, 108], [26, 0, 84 - st.stroke], 11, 9, { segs: 18, tone: 'hi', liveStroke: st.stroke > 0 });

  // 3. Coaxial Rotating Upper Punch Platter & Lower Die Turret Disc (rotates to index die #n!)
  const turretRot = ((st.dict ? 2.4 : -n * (Math.PI / 2)) + 0.35);
  // Lower heavy die bolster ring
  cad.cyl([24, 0, 22], [24, 0, 38], 50, 50, { segs: 30, holeR: 12, ribEvery: 5, tone: 'dark' });
  // Upper indexing punch turret disc
  cad.cyl([24, 0, 74], [24, 0, 84], 46, 46, { segs: 28, holeR: 10, tone: 'body' });
  // Central turret spindle column
  cad.cyl([24, 0, 38], [24, 0, 74], 10, 10, { segs: 18, tone: 'hi' });

  // 6 Hardened Cylindrical Punch & Die Bushing Stations around the Rotary Turret!
  const dieKeys = ['new', 'x', 'y', 'z', 'del', 'new'];
  for (let d = 0; d < 6; d++) {
    const a = turretRot + (d * Math.PI * 2) / 6;
    const dx = 24 + Math.cos(a) * 32, dy = Math.sin(a) * 32;
    const isCurrent = !st.dict && d === n;
    cad.cyl([dx, dy, 38], [dx, dy, 48], 8.2, 7.2, {
      segs: 16,
      holeR: 3.4,
      tone: isCurrent ? 'hi' : 'body',
      liveStroke: isCurrent,
      key: dieKeys[d],
    });
    cad.cyl([dx, dy, 63 - (isCurrent ? st.stroke : 0)], [dx, dy, 74], 6.4, 7.2, {
      segs: 16,
      tone: isCurrent ? 'hi' : 'dark',
      key: dieKeys[d],
    });
  }

  // 4. Cantilevered Front X-Y Pantograph Arm + Perforated JSObject Sheet Metal Disc/Blank!
  cad.sweepTube([[48, -46, 30], [92, -46, 38], [92, 46, 38], [48, 46, 30]], 2.8, { cornerR: 8, tone: 'body' });
  // JSObject Workpiece Sheet with punched circular in-object slot bores (+4, +8, +12)!
  cad.box3(64, -38, 40, 44, 76, 3.5, { tone: st.dict ? 'dark' : 'hi', key: 'x' });
  for (let s = 0; s < 3; s++) {
    const sy = -22 + s * 22;
    const punched = s < n;
    cad.cyl([86, sy, 43.5], [86, sy, punched ? 49 : 44.8], 7.5, 7.5, {
      segs: 16,
      holeR: punched && !st.dict ? 4.2 : 0,
      tone: punched ? 'hi' : 'dark',
      liveStroke: punched && !st.dict,
      key: ['x', 'y', 'z'][s],
    });
  }

  // Callouts
  cad.callout([86, -22, 48], 42, 36, 'PUNCH +x (@+4)', { key: 'x', op: st.props.includes('x'), sel: st.props.includes('x') });
  cad.callout([86,   0, 48], 52,  2, 'PUNCH +y (@+8)', { key: 'y', op: st.props.includes('y'), sel: st.props.includes('y') });
  cad.callout([86,  22, 48], 42, -32, 'PUNCH +z (@+12)', { key: 'z', op: st.props.includes('z'), sel: st.props.includes('z') });
  cad.callout([24, -48, 32], -46, 38, st.dict ? 'DICT MODE (HASH)' : 'DELETE (DICT)', { key: 'del', sel: st.dict });
  cad.callout([26, 0, 182], -40, -24, 'NEW BLANK (M0)', { key: 'new' });

  return st.dict
    ? 'dictionary map · slow hash table · ' + n + ' props'
    : 'map#' + n + ' {' + (st.props.map((p, i) => p + '@+' + ((i + 1) * 4)).join(', ') || 'empty') + '} · die #' + n;
}
`,
  });

  // ==========================================================================
  // FIG 4: Parser & Pre-Parser — Conical Helical Feeder Bowl & Dual Cyclones
  // ==========================================================================
  writeCadFigure({
    slug: "fig-04-parser",
    fig: "Fig 4",
    title: "Parser & Pre-Parser · Conical Spiral Bowl & Cyclones",
    hint: "vibrate spiral bowl · sort ast vs scopeinfo cyclones · drag to orbit",
    initialReadout: "lazy sort · 3 scopeinfo / 2 ast · 68 tok",
    ariaLabel:
      "3D isometric conical stainless vibratory feeder bowl mounted on three helical isolation springs with an internal climbing spiral UTF-16 token track discharging into a bifurcated Y-chute with optical flapper gate and two conical collection cyclones for AST and ScopeInfo.",
    footHelp:
      "Click parts or keys: <kbd>C</kbd> feed cold inner function (<kbd>ScopeInfo</kbd>) · <kbd>H</kbd> / <kbd>Space</kbd> feed hot eager IIFE (<kbd>AST</kbd>) · <kbd>A</kbd> feed arrow closure · <kbd>E</kbd> inject early syntax error · <kbd>Esc</kbd> empty cyclones · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit.",
    azDeg: 38,
    elDeg: 31,
    sceneJs: `
const st = { scopeCount: 3, astCount: 2, tokens: 68, gate: 'lazy', err: false, jolt: 0 };
const KM = { c: 'cold', h: 'hot', ' ': 'hot', a: 'arrow', e: 'err', Escape: 'clr' };

function act(k) {
  st.err = false;
  if (k === 'cold') { st.scopeCount++; st.tokens += 16; st.gate = 'lazy'; }
  else if (k === 'hot') { st.astCount++; st.tokens += 14; st.gate = 'eager'; }
  else if (k === 'arrow') { st.scopeCount++; st.tokens += 9; st.gate = 'lazy'; }
  else if (k === 'err') { st.err = true; st.tokens += 5; }
  else if (k === 'clr') { st.scopeCount = 0; st.astCount = 0; st.tokens = 0; st.gate = 'ready'; }
  st.jolt = 3.5;
  redraw(false);
  setTimeout(() => { st.jolt = 0; redraw(false); }, 130);
}

function buildScene(cad) {
  // 1. Circular Electromagnetic Drive Base + 3 Helical Coil Isolation Springs!
  cad.revolve(
    [[0, 52], [12, 52], [16, 44], [16, 0.5]],
    { axis: 'z', origin: [-54, 0, 0], segs: 26, tone: 'dark' }
  );
  for (let s = 0; s < 3; s++) {
    const a = (s * Math.PI * 2) / 3 + 0.4;
    const sx = -54 + Math.cos(a) * 36, sy = Math.sin(a) * 36;
    cad.sweepTube(cad.helix3D(sx, sy, 6.5, 6.5, 14, 34 + st.jolt, 3.5, 28), 1.6, { segs: 8, tone: 'hi' });
  }

  // 2. Open Conical Stepped Vibratory Feeder Bowl (doubleSided so you see INSIDE the bowl!)
  const bz = 34 + st.jolt;
  cad.revolve(
    [[bz, 0.5], [bz, 38], [bz + 16, 52], [bz + 34, 64], [bz + 52, 68]],
    { axis: 'z', origin: [-54, 0, 0], segs: 32, doubleSided: true, ribRings: [1, 2, 3], tone: 'body', key: 'cold' }
  );
  // Central conical dome inside the bowl floor
  cad.revolve(
    [[bz, 28], [bz + 20, 9], [bz + 23, 0.4]],
    { axis: 'z', origin: [-54, 0, 0], segs: 20, tone: 'hi', key: 'cold' }
  );
  // Real 3D Climbing Helical Spiral Track + Token Pellets winding up the inside wall!
  const spiral = cad.helix3D(-54, 0, 35, 63, bz + 6, bz + 48, 2.15, 44);
  cad.sweepTube(spiral, 3.2, { segs: 10, tone: 'hi', liveStroke: true, key: 'hot' });
  for (const ti of [10, 22, 34, 41]) {
    const p = spiral[ti];
    cad.cyl([p[0], p[1], p[2] + 2], [p[0], p[1], p[2] + 6.5], 3.8, 3.8, { segs: 10, tone: 'hi', key: 'hot' });
  }

  // 3. Tangential Linear Outfeed Chute + Overhead Optical Ring Sensor + Bifurcated Y-Diverter!
  cad.sweepTube([[-4, -56, bz + 44], [46, -24, 62]], 6.5, { segs: 14, tone: 'body' });
  // Optical Scanner Ring Collar around chute
  cad.cyl([18, -42, 71], [28, -36, 68], 14, 14, { segs: 18, holeR: 9, tone: st.err ? 'dark' : 'hi', liveStroke: !st.err, key: 'err' });

  // Pivoting Optical Flapper Diverter Vane at Y-Junction (x=48, y=-22, z=62)
  const flapYaw = st.gate === 'eager' ? 0.45 : -0.45;
  cad.push(cad.mTrans(48, -22, 62));
  cad.push(cad.mRotZ(flapYaw));
  cad.box3(-2, -3, -6, 26, 6, 14, { tone: 'hi', liveStroke: true, key: 'hot' });
  cad.pop(); cad.pop();

  // Two Divergent Discharge Tubes feeding Eager AST Cyclone vs Lazy ScopeInfo Cyclone!
  cad.sweepTube([[50, -22, 60], [98, -58, 50]], 5.2, { tone: st.gate === 'eager' ? 'hi' : 'body', key: 'hot' });
  cad.sweepTube([[50, -22, 60], [98,  26, 50]], 5.2, { tone: st.gate === 'lazy' ? 'hi' : 'body', key: 'cold' });

  // 4. Two Round Conical Hopper Cyclones on Tripod Legs (AST Cyclone vs ScopeInfo Cyclone!)
  function drawCyclone(cx, cy, count, active, keyId) {
    for (let l = 0; l < 3; l++) {
      const a = (l * Math.PI * 2) / 3 + 0.2;
      cad.sweepTube([[cx + Math.cos(a)*24, cy + Math.sin(a)*24, 0], [cx + Math.cos(a)*20, cy + Math.sin(a)*20, 32]], 1.8, { tone: 'dark' });
    }
    cad.revolve(
      [[8, 4], [28, 22], [58, 24], [64, 26]],
      { axis: 'z', origin: [cx, cy, 0], segs: 22, doubleSided: true, ribRings: [1, 2], tone: active ? 'hi' : 'body', liveStroke: active, key: keyId }
    );
    // Stacked collected rings inside cyclone proportional to count
    const fillH = Math.min(54, 30 + count * 4.5);
    cad.cyl([cx, cy, 26], [cx, cy, fillH], 16, 19, { segs: 18, tone: 'hi', key: keyId });
  }
  drawCyclone(112, -66, st.astCount, st.gate === 'eager' && !st.err, 'hot');
  drawCyclone(112,  36, st.scopeCount, st.gate === 'lazy' && !st.err, 'cold');

  // Callouts (kept outside bowl rim so helical track is 100% unobstructed!)
  cad.callout([-96, 46, bz + 34], -42, 24, 'FEED COLD FN (LAZY)', { key: 'cold', sel: st.gate === 'lazy' });
  cad.callout([112, -66, 62], 36, -28, 'HOT IIFE -> AST (' + st.astCount + ')', { key: 'hot', op: true, sel: st.gate === 'eager' });
  cad.callout([112,  36, 62], 38, 28, 'SCOPEINFO (' + st.scopeCount + ')', { key: 'arrow', sel: st.gate === 'lazy' });
  cad.callout([22, -40, 84], 24, -44, st.err ? 'SYNTAX ERR!' : 'EARLY ERR GATE', { key: 'err', sel: st.err });
  cad.callout([-54, 48, 6], -44, 46, 'EMPTY CYCLONES', { key: 'clr' });

  return st.err
    ? 'early syntax error · rejected at gate · ' + st.tokens + ' tok'
    : st.gate + ' sort · ' + st.scopeCount + ' scopeinfo / ' + st.astCount + ' ast · ' + st.tokens + ' tok';
}
`,
  });
}
