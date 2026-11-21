import { writeIsoFigure } from "./iso-shell.mjs";

export function buildFigs5To8() {
  // ==========================================================================
  // FIG 5: Ignition (Bytecode Interpreter) — 24V Starter Motor & Fuel Rail
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-05-ignition",
    fig: "Fig 5",
    title: "Ignition · 24V Starter Motor & Bytecode Rail",
    hint: "crank 24v · step bytecode injectors 1-4",
    initialReadout: "24v cranked · inj #2 Add · acc 43 · warm 1",
    ariaLabel:
      "Isometric 24V electric starter motor with cooling fins and piggyback solenoid driving a four-injector common bytecode fuel rail for V8 Ignition.",
    footHelp:
      "Keys: <kbd>C</kbd> crank 24V starter · <kbd>Space</kbd> step bytecode injector · <kbd>1</kbd>–<kbd>4</kbd> fire injector (<code>LdaSmi</code>, <code>Add</code>, <code>Star r0</code>, <code>Return</code>) · <kbd>K</kbd> cut ignition.",
    bounds: [
      [0, 0, 0, 392, 212, 134],
    ],
    sceneJs: `
let svg = '';
// 1. Engine Bed & Cradle Base (388 x 208 x 16)
svg += box(0, 0, 0, 388, 208, 16, 5);

// 2. Back-Right 24V ECU & Accumulator Telemetry Panel (x = 160, y = 8, z = 16..118)
svg += box(160, 8, 16, 214, 34, 102, 4);
svg += \`<g transform="\${FRONT(160, 42, 118)}">
  <defs><clipPath id="igScr"><rect x="10" y="9" width="194" height="54" rx="4"/></clipPath></defs>
  <rect class="face glass" x="10" y="9" width="194" height="54" rx="4"/>
  <g clip-path="url(#igScr)">
    <text id="igVolt" class="lcd" x="16" y="22" font-size="8.5">24.2V BUS · RAIL 380 kPa · PC=0x02</text>
    <text id="igOp" class="lcd-dim" x="16" y="36" font-size="8.2">OP: Add r0, [feedback #0]</text>
    <text id="igRegs" class="lcd" x="16" y="50" font-size="8.5">acc = 43 · r0 = 42 · warm = 1</text>
  </g>
</g>\`;

// 3. Left Horizontal 24V Electric Starter Motor + Solenoid (x = 16..148, y = 46..126)
svg += box(24, 54, 16, 108, 62, 16, 2); // motor saddle mount
svg += \`<g class="unit" id="starterMotor">
  \${box(16, 46, 32, 122, 78, 60, 8)}
  <!-- 10 axial stator cooling fins on TOP and FRONT -->
  <g transform="\${TOP(16, 46, 92)}">
    \${Array.from({length:9},(_,i)=>\`<path class="detail" d="M\${16+i*11} 8v62"/>\`).join('')}
  </g>
  <g transform="\${FRONT(16, 124, 92)}">
    \${Array.from({length:9},(_,i)=>\`<path class="detail" d="M\${16+i*11} 8v44"/>\`).join('')}
  </g>
  <!-- Piggyback 24V Starter Solenoid on top of motor -->
  \${box(32, 58, 92, 84, 46, 26, 6)}
  <g transform="\${FRONT(32, 104, 118)}"><text class="lbl-hi" x="42" y="16" font-size="7.5">24V SOLENOID</text></g>
  <!-- Drive Pinion Nose Cone engaging rail pump -->
  \${box(138, 68, 48, 18, 34, 28, 4)}
</g>\`;

// 4. Intake Runner Manifold Block + 4 Bytecode Fuel Injectors + Common Fuel Rail (x = 158..374, y = 56..126)
svg += box(158, 54, 16, 214, 72, 34, 4); // lower intake manifold
const INJS = [
  ['LdaSmi', 172],
  ['Add', 222],
  ['Star r0', 272],
  ['Return', 322]
];
INJS.forEach(([lbl, ix], i) => {
  // Intake port boss + vertical stepped fuel injector body
  svg += box(ix + 4, 72, 50, 26, 32, 12, 3);
  svg += \`<g class="unit" id="inj\${i}">
    \${box(ix, 68, 62, 34, 40, 28, 5)}
    <g transform="\${FRONT(ix, 108, 90)}"><text x="17" y="17" font-size="6.8" class="lbl-hi">\${lbl}</text></g>
  </g>\`;
});
// Elevated Common Bytecode Fuel Rail spanning across top of all 4 injectors (z = 90..108)
svg += box(154, 72, 90, 222, 32, 16, 5);
svg += \`<g transform="\${TOP(154, 72, 106)}">
  <path class="detail" d="M12 16h198"/>
  <text class="lbl-hi" x="111" y="12" font-size="7.2">COMMON BYTECODE RAIL</text>
</g>\`;

// 5. Front Operator Switchgear Manifold (y = 148..194)
const BTNS = [
  ['crank', 'CRANK 24V', 18, 72, true],
  ['step', 'STEP OP', 96, 64, true],
  ['i0', '1:LDA', 166, 46, false],
  ['i1', '2:ADD', 218, 46, false],
  ['i2', '3:STAR', 270, 48, false],
  ['cut', 'CUT', 324, 48, false]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 152, 16, bw, 36, 8, 3)}<g transform="\${TOP(bx, 152, 24)}"><text x="\${bw/2}" y="21" font-size="7.8">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const OPS = [
  { name: 'LdaSmi [21]', fn: s => { s.acc = 21; } },
  { name: 'Add r0, [0]', fn: s => { s.acc = s.acc + s.r0; } },
  { name: 'Star r0', fn: s => { s.r0 = s.acc; } },
  { name: 'Return (tier check)', fn: s => { s.warm++; } }
];
const st = { running: true, pc: 1, acc: 43, r0: 22, warm: 1 };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function pulseMotor() {
  const m = $('starterMotor');
  m.style.transform = 'translateY(2.5px)';
  setTimeout(() => { m.style.transform = ''; }, 110);
}

function render() {
  $('starterMotor').classList.toggle('lit', st.running);
  for (let i = 0; i < 4; i++) {
    const inj = $('inj' + i);
    const active = st.running && st.pc === i;
    inj.classList.toggle('lit', active);
    inj.style.transform = active ? 'translateY(3px)' : '';
  }
  if (!st.running) {
    $('igVolt').textContent = '0.0V · RAIL DEPRESSURIZED (NO JIT)';
    $('igOp').textContent = 'BYTECODE HALTED · V8 CANNOT START';
    $('igRegs').textContent = 'acc = ' + st.acc + ' · r0 = ' + st.r0;
    $('readout').textContent = 'ignition off · 0 kPa · baseline required';
  } else {
    $('igVolt').textContent = '24.2V · RAIL 380 kPa · PC=0x0' + st.pc;
    $('igOp').textContent = 'FIRE INJ #' + (st.pc + 1) + ': ' + OPS[st.pc].name;
    $('igRegs').textContent = 'acc = ' + st.acc + ' · r0 = ' + st.r0 + ' · loops = ' + st.warm;
    $('readout').textContent = '24v on · inj #' + (st.pc + 1) + ' ' + INJS[st.pc][0] + ' · acc ' + st.acc + ' · warm ' + st.warm;
  }
  keys.get('crank').classList.toggle('sel', st.running);
}

function fire(idx) {
  st.running = true;
  st.pc = idx % 4;
  OPS[st.pc].fn(st);
  pulseMotor();
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'crank') { st.running = true; pulseMotor(); }
  else if (k === 'cut') { st.running = false; }
  else if (k === 'step') { fire((st.pc + 1) % 4); }
  else if (k === 'i0') fire(0);
  else if (k === 'i1') fire(1);
  else if (k === 'i2') fire(2);
  else if (k === 'i3') fire(3);
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { 'c':'crank', ' ':'step', 'Enter':'step', '1':'i0', '2':'i1', '3':'i2', '4':'i3', 'k':'cut', 'Escape':'cut' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });

  // ==========================================================================
  // FIG 6: Torque & CSA — 4-Post Progressive Stamping Dies & Hardened Jig
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-06-torque-csa",
    fig: "Fig 6",
    title: "Torque & CSA · Progressive Stamping Die Press",
    hint: "strike bolster · advance 4 progressive stations",
    initialReadout: "station 4/4 · stamped ArrayPrototypePush · 3 stubs",
    ariaLabel:
      "Isometric four-pillar progressive stamping die press for V8 Torque and CodeStubAssembler, feeding strip stock across four hardened die stations beneath a descending upper ram platen.",
    footHelp:
      "Keys: <kbd>Space</kbd> or <kbd>S</kbd> strike progressive die · <kbd>T</kbd> switch <code>.tq</code> built-in target · <kbd>R</kbd> reset strip coil.",
    bounds: [
      [0, 0, 0, 384, 218, 174],
    ],
    sceneJs: `
let svg = '';
// 1. Heavy Lower Bolster / Die Shoe (380 x 154 x 28) with T-slots
svg += box(0, 8, 0, 380, 154, 28, 4);
svg += \`<g transform="\${FRONT(0, 162, 28)}">
  \${[44, 126, 208, 290].map(tx => \`<rect class="face glass" x="\${tx}" y="8" width="42" height="10" rx="1.5"/>\`).join('')}
</g>\`;

// 2. Back Guide Pillars (z = 28..148)
svg += box(14, 16, 28, 20, 20, 120, 3);
svg += box(346, 16, 28, 20, 20, 120, 3);

// 3. Lower Hardened Die Blocks — 4 Progressive Stations + Strip-Stock Ribbon (y = 60..112)
const STATIONS = [
  ['S1: .tq AST', 48],
  ['S2: CSA CFG', 124],
  ['S3: BOUNDS', 200],
  ['S4: HANDLER', 276]
];
// Continuous steel coil strip running across all 4 stations
svg += box(36, 74, 42, 308, 28, 4, 1);
STATIONS.forEach(([lbl, sx], i) => {
  svg += \`<g class="unit" id="dieSt\${i}">
    \${box(sx, 62, 28, 62, 52, 14, 3)}
    \${box(sx + 8, 76, 46, 46, 24, 9, 2)}
    <g transform="\${FRONT(sx, 114, 42)}"><text x="31" y="10" font-size="6.4" class="lbl-hi">\${lbl}</text></g>
  </g>\`;
});

// 4. Front Guide Pillars (painted BEFORE/WITH upper bolster so pillars frame the die window)
svg += box(14, 134, 28, 20, 20, 120, 3);
svg += box(346, 134, 28, 20, 20, 120, 3);

// 5. Massive Moving Upper Ram Platen + 4 Descending Punches + Crown Housing (id="upperBolster")
svg += \`<g class="unit" id="upperBolster">
  \${[48, 124, 200, 276].map(sx => box(sx + 14, 72, 92, 34, 32, 18, 2)).join('')}
  \${box(6, 12, 110, 368, 146, 26, 4)}
  \${box(86, 30, 136, 208, 108, 34, 5)}
  <g transform="\${FRONT(86, 138, 170)}">
    <defs><clipPath id="tqScr"><rect x="12" y="6" width="184" height="22" rx="3"/></clipPath></defs>
    <rect class="face glass" x="12" y="6" width="184" height="22" rx="3"/>
    <g clip-path="url(#tqScr)">
      <text id="tqTarget" class="lcd" x="18" y="20" font-size="8.2">TARGET: ArrayPrototypePush.tq [4/4]</text>
    </g>
  </g>
</g>\`;

// 6. Dual-Palm Operator Stamping Bar in Front (y = 172..212)
const BTNS = [
  ['strike', 'STRIKE PROGRESSIVE DIE', 22, 152, true],
  ['spec', 'NEXT .TQ TARGET', 182, 112, false],
  ['rst', 'RESET COIL', 302, 68, false]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 174, 0, bw, 36, 12, 3)}<g transform="\${TOP(bx, 174, 12)}"><text x="\${bw/2}" y="21.5" font-size="7.8">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const TARGETS = ['ArrayPrototypePush', 'LoadIC_BytecodeHandler', 'StringAdd_CheckNone', 'FastNewObjectStub'];
const st = { step: 4, targetIdx: 0, stamped: 3 };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function slamBolster() {
  const b = $('upperBolster');
  b.style.transform = 'translateY(11px)';
  setTimeout(() => { b.style.transform = ''; }, 145);
}

function render() {
  const tName = TARGETS[st.targetIdx];
  $('tqTarget').textContent = 'TQ: ' + tName + ' [' + st.step + '/4]';
  for (let i = 0; i < 4; i++) {
    $('dieSt' + i).classList.toggle('lit', i < st.step);
  }
  $('readout').textContent = 'station ' + st.step + '/4 · ' + tName + ' · ' + st.stamped + ' built-ins';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'strike') {
    slamBolster();
    if (st.step < 4) st.step++;
    else { st.stamped++; st.step = 1; st.targetIdx = (st.targetIdx + 1) % TARGETS.length; }
  } else if (k === 'spec') {
    st.targetIdx = (st.targetIdx + 1) % TARGETS.length;
    st.step = 1;
  } else if (k === 'rst') {
    st.step = 0;
  }
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { ' ':'strike', 'Enter':'strike', 's':'strike', 't':'spec', 'r':'rst', 'Escape':'rst' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });

  // ==========================================================================
  // FIG 7: Orinoco Old Space — Automated AS/RS High-Bay Warehouse & Laser Crane
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-07-old-space",
    fig: "Fig 7",
    title: "Orinoco Old Space · AS/RS High-Bay Warehouse",
    hint: "laser-mark rack · sweep white · compact bays",
    initialReadout: "as/rs rack · 6 live / 3 dead · 25% frag",
    ariaLabel:
      "Isometric tall AS/RS high-bay warehouse rack with 12 three-dimensional Old-Space memory pallets, a traveling stacker-crane mast with vertical laser inventory scanner, and mark-sweep-compact controls.",
    footHelp:
      "Keys: <kbd>A</kbd> store Old-Space pallet · <kbd>U</kbd> orphan a pallet (unroot) · <kbd>L</kbd> laser tricolor mark · <kbd>S</kbd> sweep white pallets · <kbd>C</kbd> compact high-bay rack.",
    bounds: [
      [0, 0, 0, 426, 198, 196],
    ],
    sceneJs: `
let svg = '';
// 1. Warehouse Floor Slab (424 x 194 x 14)
svg += box(0, 0, 0, 424, 194, 14, 4);

// 2. Tall 4-Col x 3-Tier AS/RS High-Bay Storage Rack (x = 18..266, y = 12..64, z = 14..180)
// Back Uprights first, then strictly tier-by-tier (shelf -> pallets) for true painter's order!
for (let c = 0; c <= 4; c++) { svg += box(18 + c * 60, 12, 14, 8, 10, 166, 1); }
for (let tier = 0; tier < 3; tier++) {
  svg += box(18, 12, 14 + tier * 52, 248, 52, 6, 1);
  for (let col = 0; col < 4; col++) {
    const idx = tier * 4 + col;
    const px = 30 + col * 60, py = 20, pz = 20 + tier * 52;
    svg += \`<g class="unit" id="bay\${idx}">
      \${box(px, py, pz, 42, 38, 30, 3)}
      <g transform="\${FRONT(px, py + 38, pz + 30)}"><text id="bayTxt\${idx}" x="21" y="18" font-size="7.2" class="lbl-hi">LIVE</text></g>
    </g>\`;
  }
}
// Top Rack Cap Shelf + Front Upright Columns
svg += box(18, 12, 170, 248, 52, 6, 1);
for (let c = 0; c <= 4; c++) { svg += box(18 + c * 60, 56, 14, 8, 8, 162, 1); }

// 3. Right WMS Inventory & Compaction Control Tower (x = 318..410, completely clear of col 3!)
svg += box(318, 28, 14, 92, 96, 118, 5);
svg += \`<g transform="\${FRONT(318, 124, 132)}">
  <defs><clipPath id="whScr"><rect x="8" y="10" width="76" height="72" rx="4"/></clipPath></defs>
  <rect class="face glass" x="8" y="10" width="76" height="72" rx="4"/>
  <g clip-path="url(#whScr)">
    <text class="lcd-dim" x="13" y="23" font-size="7">OLD-SPACE WMS</text>
    <text id="whLive" class="lcd" x="13" y="37" font-size="8">BLACK: 6 BAYS</text>
    <text id="whDead" class="lcd-dim" x="13" y="50" font-size="7.5">WHITE: 3 BAYS</text>
    <text id="whFrag" class="lcd" x="13" y="64" font-size="7.8">FRAG: 25%</text>
    <text id="whPhase" class="lcd-dim" x="13" y="76" font-size="6.8">READY</text>
  </g>
</g>\`;

// 4. AS/RS Crane Floor Guide Rail + Traveling Vertical Mast & Laser Scanner Carriage (y = 82..114)
svg += box(16, 86, 14, 254, 16, 5, 2);
svg += \`<g class="unit" id="craneMast">
  \${box(38, 80, 19, 28, 28, 10, 2)}
  \${box(47, 89, 29, 10, 10, 158, 2)}
  <g class="unit lit" id="laserCarriage">
    \${box(34, 74, 72, 36, 26, 18, 3)}
    <g transform="\${FRONT(34, 100, 90)}"><text x="18" y="12" font-size="6.2" class="lbl-hi">LASER</text></g>
  </g>
</g>\`;

// 5. Front Warehouse Dock Keypad (y = 140..182)
const BTNS = [
  ['alloc', '+PALLET', 18, 62, false],
  ['drop', 'UNROOT', 86, 62, false],
  ['mark', 'LASER MARK', 154, 76, true],
  ['sweep', 'SWEEP', 236, 58, false],
  ['compact', 'COMPACT', 300, 68, true]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 142, 14, bw, 36, 8, 3)}<g transform="\${TOP(bx, 142, 22)}"><text x="\${bw/2}" y="21" font-size="7.5">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

// 12 bays: null = empty, { root: bool, marked: bool }
const st = {
  bays: [
    { root: true, marked: true }, null, { root: false, marked: false }, { root: true, marked: true },
    { root: true, marked: true }, { root: false, marked: false }, { root: true, marked: true }, null,
    { root: false, marked: false }, { root: true, marked: true }, null, { root: true, marked: true }
  ],
  craneCol: 1,
  craneTier: 1,
  phase: 'READY'
};
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function render() {
  // Move AS/RS Crane along aisle (+x) and Laser Shuttle vertically (-z)
  const dx = st.craneCol * 60;
  const mastPt = [dx * Math.cos(Math.PI/6), dx * Math.sin(Math.PI/6)];
  $('craneMast').style.transform = \`translate(\${mastPt[0].toFixed(1)}px, \${mastPt[1].toFixed(1)}px)\`;
  $('laserCarriage').style.transform = \`translateY(\${((1 - st.craneTier) * 52).toFixed(1)}px)\`;

  let live = 0, dead = 0, holes = 0, lastUsed = -1;
  st.bays.forEach((b, idx) => {
    const el = $('bay' + idx), txt = $('bayTxt' + idx);
    if (!b) {
      el.style.display = 'none';
    } else {
      el.style.display = '';
      lastUsed = idx;
      if (b.root) live++; else dead++;
      const isBlack = b.root && b.marked;
      el.classList.toggle('lit', isBlack);
      el.classList.toggle('mid', !isBlack);
      txt.textContent = isBlack ? 'BLACK' : (b.root ? 'ROOT' : 'WHITE');
    }
  });
  for (let i = 0; i < lastUsed; i++) if (!st.bays[i]) holes++;
  const frag = lastUsed >= 0 ? Math.round((holes / (lastUsed + 1)) * 100) : 0;

  $('whLive').textContent = 'LIVE: ' + live + ' BAYS';
  $('whDead').textContent = 'WHITE: ' + dead + ' BAYS';
  $('whFrag').textContent = 'FRAG: ' + frag + '%';
  $('whPhase').textContent = st.phase;
  $('readout').textContent = st.phase.toLowerCase() + ' · ' + live + ' live / ' + dead + ' dead · ' + frag + '% frag';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'alloc') {
    const idx = st.bays.findIndex(b => b === null);
    if (idx >= 0) {
      st.bays[idx] = { root: true, marked: false };
      st.craneCol = idx % 4; st.craneTier = Math.floor(idx / 4);
      st.phase = 'STORED BAY #' + idx;
    } else st.phase = 'RACK FULL (12/12)';
  } else if (k === 'drop') {
    const idx = st.bays.findIndex(b => b && b.root);
    if (idx >= 0) {
      st.bays[idx].root = false; st.bays[idx].marked = false;
      st.craneCol = idx % 4; st.craneTier = Math.floor(idx / 4);
      st.phase = 'UNROOTED BAY #' + idx;
    }
  } else if (k === 'mark') {
    st.bays.forEach(b => { if (b) b.marked = b.root; });
    st.craneCol = (st.craneCol + 1) % 4;
    st.craneTier = (st.craneTier + 1) % 3;
    st.phase = 'LASER MARKED';
  } else if (k === 'sweep') {
    let freed = 0;
    st.bays = st.bays.map(b => {
      if (b && !b.root) { freed++; return null; }
      return b;
    });
    st.craneCol = 2; st.craneTier = 0;
    st.phase = 'SWEPT ' + freed + ' WHITE';
  } else if (k === 'compact') {
    const survivors = st.bays.filter(b => b && b.root).map(b => ({ root: true, marked: true }));
    while (survivors.length < 12) survivors.push(null);
    st.bays = survivors;
    st.craneCol = Math.max(0, (survivors.filter(Boolean).length - 1) % 4);
    st.craneTier = 0;
    st.phase = 'COMPACTED 0% FRAG';
  }
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { 'a':'alloc', 'u':'drop', 'l':'mark', 'm':'mark', 's':'sweep', 'c':'compact', ' ':'compact' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });

  // ==========================================================================
  // FIG 8: Orinoco New Space (Scavenger) — Dual-Belt Eddy-Current Separator
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-08-new-space",
    fig: "Fig 8",
    title: "Orinoco New Space · Eddy-Current Chip Separator",
    hint: "feed nursery · pulse eddy rotor · promote age 2",
    initialReadout: "scavenger · 2 to-space / 4 dropped · 1 promoted",
    ariaLabel:
      "Isometric dual-belt eddy-current chip separator for V8 Orinoco New Space Scavenger: elevated From-Space belt, magnetic eddy-current drum, zero-cost dead-chip gravity chute, lower To-Space survivor belt, and Old-Space promotion elevator.",
    footHelp:
      "Keys: <kbd>F</kbd> feed Nursery allocation · <kbd>D</kbd> die young (mark batch unreachable) · <kbd>Space</kbd> or <kbd>S</kbd> scavenge pulse · <kbd>P</kbd> promote age-2 survivors to Old Space · <kbd>Esc</kbd> reset.",
    bounds: [
      [0, 0, 0, 404, 198, 138],
    ],
    sceneJs: `
let svg = '';
// 1. Separator Plant Floor Frame (400 x 194 x 12)
svg += box(0, 0, 0, 400, 194, 12, 4);

// 2. Back-Left Scavenger Telemetry Unit (x = 14, y = 8, z = 12..132)
svg += box(14, 8, 12, 152, 30, 120, 4);
svg += \`<g transform="\${FRONT(14, 38, 132)}">
  <defs><clipPath id="scvScr"><rect x="8" y="8" width="136" height="44" rx="3"/></clipPath></defs>
  <rect class="face glass" x="8" y="8" width="136" height="44" rx="3"/>
  <g clip-path="url(#scvScr)">
    <text id="scvHead" class="lcd" x="13" y="21" font-size="7.8">CHENEY SEMI-SPACE SCAVENGER</text>
    <text id="scvSub" class="lcd-dim" x="13" y="34" font-size="7.4">DEAD DROP = 0 CYC · COPY LIVE</text>
    <text id="scvCounts" class="lcd" x="13" y="46" font-size="7.8">TO: 2 · DROPPED: 4 · OLD: 1</text>
  </g>
</g>\`;

// 3. Upper-Left From-Space Trestle + Elevated Feeder Conveyor Belt (x = 14..186, y = 48..112, z = 12..86)
svg += box(24, 54, 12, 20, 52, 60, 2);
svg += box(136, 54, 12, 20, 52, 60, 2);
svg += box(12, 48, 72, 174, 64, 14, 5);
svg += \`<g transform="\${TOP(12, 48, 86)}">
  \${Array.from({length:8},(_,i)=>\`<path class="detail" d="M\${16+i*20} 6v52"/>\`).join('')}
  <text class="lbl" x="87" y="58" font-size="6.8">FROM-SPACE NURSERY</text>
</g>\`;
// 3 Nursery Chip Allocations sitting on Upper From-Space Belt
for (let i = 0; i < 3; i++) {
  const cx = 28 + i * 46;
  svg += \`<g class="unit" id="fromChip\${i}">\${box(cx, 64, 86, 32, 28, 10, 2)}<g transform="\${TOP(cx, 64, 96)}"><text id="fromTxt\${i}" x="16" y="17" font-size="6.8" class="top-lbl">NEW</text></g></g>\`;
}

// 4. Central Dead-Chip Gravity Drop Bin (directly beneath drum at z = 12..48)
svg += box(172, 50, 12, 62, 62, 36, 3);
svg += \`<g transform="\${FRONT(172, 112, 48)}"><text id="dropBinTxt" class="lbl-hi" x="31" y="21" font-size="7.2">4 DROPPED</text></g>\`;

// 5. Eddy-Current Magnetic Rotor Drum Housing (x = 178..232, y = 44..116, z = 58..102)
svg += \`<g class="unit lit" id="eddyDrum">
  \${box(178, 44, 58, 54, 72, 44, 7)}
  <g transform="\${FRONT(178, 116, 102)}">
    <circle class="struct" cx="27" cy="22" r="15"/>
    <path id="rotorCross" class="live-stroke" d="M15 22h24M27 10v24"/>
  </g>
</g>\`;

// 6. Lower-Right To-Space Survivor Belt (x = 240..348, y = 52..110, z = 12..38) + Far-Right Old-Space Elevator
svg += box(240, 52, 12, 108, 58, 26, 4);
svg += \`<g transform="\${TOP(240, 52, 38)}">
  \${Array.from({length:5},(_,i)=>\`<path class="detail" d="M\${16+i*20} 6v46"/>\`).join('')}
</g>\`;
// 2 Survivor Chips leaping onto To-Space Belt
for (let i = 0; i < 2; i++) {
  const sx = 248 + i * 44;
  svg += \`<g class="unit lit" id="toChip\${i}">\${box(sx, 66, 38, 34, 30, 11, 2)}<g transform="\${TOP(sx, 66, 49)}"><text id="toTxt\${i}" x="17" y="18" font-size="6.8" class="top-lbl">AGE 1</text></g></g>\`;
}
// Far-Right Old-Space Promotion Elevator Tower (x = 358..396, y = 46..114, z = 12..114)
svg += box(358, 46, 12, 38, 68, 102, 4);
svg += \`<g transform="\${FRONT(358, 114, 114)}">
  <rect class="face glass" x="6" y="12" width="26" height="58" rx="2"/>
  <text id="promoTxt" class="lcd" x="19" y="44" font-size="8.5" text-anchor="middle">1</text>
  <text class="lbl" x="19" y="84" font-size="6.2">OLD</text>
</g>\`;

// 7. Front Operator Bar (y = 138..182)
const BTNS = [
  ['feed', 'FEED NURSERY', 16, 84, false],
  ['die', 'DIE YOUNG', 106, 74, false],
  ['scav', 'SCAVENGE PULSE', 186, 98, true],
  ['promo', 'PROMOTE', 290, 60, true],
  ['rst', 'CLR', 356, 34, false]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 140, 12, bw, 36, 8, 3)}<g transform="\${TOP(bx, 140, 20)}"><text x="\${bw/2}" y="21" font-size="7.4">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = {
  nursery: [{ live: true }, { live: false }, { live: true }],
  toSpace: [{ age: 1 }, { age: 2 }],
  dropped: 4,
  promoted: 1,
  spin: false
};
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function flashDrum() {
  const d = $('eddyDrum');
  d.style.transform = 'translateY(-3px)';
  st.spin = !st.spin;
  $('rotorCross').setAttribute('d', st.spin ? 'M17 12l20 20M37 12l-20 20' : 'M15 22h24M27 10v24');
  setTimeout(() => { d.style.transform = ''; }, 130);
}

function render() {
  for (let i = 0; i < 3; i++) {
    const c = st.nursery[i], el = $('fromChip' + i), t = $('fromTxt' + i);
    if (!c) el.style.display = 'none';
    else {
      el.style.display = '';
      el.classList.toggle('lit', c.live);
      t.textContent = c.live ? 'ROOT' : 'DEAD';
    }
  }
  for (let i = 0; i < 2; i++) {
    const s = st.toSpace[i], el = $('toChip' + i), t = $('toTxt' + i);
    if (!s) el.style.display = 'none';
    else {
      el.style.display = '';
      t.textContent = 'AGE ' + s.age;
    }
  }
  $('dropBinTxt').textContent = st.dropped + ' DROPPED';
  $('promoTxt').textContent = String(st.promoted);
  $('scvCounts').textContent = 'TO: ' + st.toSpace.length + ' · DROPPED: ' + st.dropped + ' · OLD: ' + st.promoted;
  $('readout').textContent = 'scavenger · ' + st.toSpace.length + ' to-space / ' + st.dropped + ' dropped · ' + st.promoted + ' promoted';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'feed') {
    st.nursery = [{ live: true }, { live: false }, { live: (st.dropped % 2) === 0 }];
  } else if (k === 'die') {
    st.nursery.forEach((c, idx) => { if (c && idx > 0) c.live = false; });
  } else if (k === 'scav') {
    flashDrum();
    const survivors = [];
    st.nursery.forEach(c => {
      if (!c) return;
      if (c.live) survivors.push({ age: 1 });
      else st.dropped++;
    });
    st.nursery = [null, null, null];
    st.toSpace = [...st.toSpace.map(s => ({ age: s.age + 1 })), ...survivors];
    // Auto-promote any age >= 2 if more than 2 on belt
    while (st.toSpace.length > 2) {
      st.toSpace.shift();
      st.promoted++;
    }
  } else if (k === 'promo') {
    const kept = [];
    st.toSpace.forEach(s => {
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
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { 'f':'feed', 'd':'die', 's':'scav', ' ':'scav', 'Enter':'scav', 'p':'promo', 'Escape':'rst' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });
}
