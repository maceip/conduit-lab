import { writeIsoFigure } from "./iso-shell.mjs";

export function buildFigs1To4() {
  // ==========================================================================
  // FIG 1: v8::Isolate — Self-Contained Modular Factory Skid
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-01-isolate",
    fig: "Fig 1",
    title: "v8::Isolate · Modular Factory Skid",
    hint: "lock thread · spawn realm · drain microtasks",
    initialReadout: "thread #1 locked · 1 realm · cage 4096 MiB",
    ariaLabel:
      "Isometric v8::Isolate modular factory skid with forklift pockets, 4 GiB pointer-compression cage bollards, NEMA control cabinet, twin heap reservation tanks, and thread-lockout controls.",
    footHelp:
      "Controls: <kbd>1</kbd> lock Thread #1 · <kbd>2</kbd> contend Thread #2 · <kbd>U</kbd> unlock v8::Locker · <kbd>R</kbd> spawn Context/Realm · <kbd>M</kbd> enqueue microtask · <kbd>D</kbd> drain queue.",
    bounds: [
      [0, 0, 0, 340, 226, 18],
      [14, 14, 18, 126, 68, 118],
      [158, 18, 18, 72, 68, 102],
      [244, 18, 18, 72, 68, 86],
      [0, 0, 18, 340, 226, 118],
    ],
    sceneJs: `
let svg = '';
// 1. Heavy structural steel Skid Base (340 x 226 x 18) with forklift pockets & floor deck grid
svg += box(0, 0, 0, 340, 226, 18, 4);
svg += \`<g transform="\${FRONT(0, 226, 18)}">
  <rect class="face glass" x="52" y="5" width="46" height="9" rx="1.5"/>
  <rect class="face glass" x="236" y="5" width="46" height="9" rx="1.5"/>
  \${Array.from({length:15},(_,i)=>\`<path class="detail" d="M\${14+i*22} 2v2"/>\`).join('')}
</g>\`;
svg += \`<g transform="\${SIDE(340, 226, 18)}">
  <rect class="face glass" x="48" y="5" width="40" height="9" rx="1.5"/>
  <rect class="face glass" x="138" y="5" width="40" height="9" rx="1.5"/>
</g>\`;
// Checker-plate deck grid inside 4 GiB cage perimeter
svg += \`<g transform="\${TOP(0, 0, 18)}">
  <rect class="detail" x="10" y="10" width="320" height="206" rx="3"/>
  \${Array.from({length:7},(_,i)=>\`<path class="detail" d="M10 \${36+i*26}h320"/>\`).join('')}
  \${Array.from({length:9},(_,i)=>\`<path class="detail" d="M\${38+i*34} 10v206"/>\`).join('')}
</g>\`;

// 2. Back corner bollards (4 GiB Pointer-Compression Cage boundary)
svg += box(6, 6, 18, 10, 10, 96, 2);
svg += box(324, 6, 18, 10, 10, 96, 2);
// Back perimeter cage rail
svg += box(16, 8, 92, 308, 6, 6, 1);

// 3. Back-left NEMA VM Control & v8::Locker Cabinet
svg += box(20, 20, 18, 124, 66, 114, 5);
svg += \`<g transform="\${SIDE(144, 86, 132)}">
  \${Array.from({length:8},(_,i)=>\`<path class="detail" d="M14 \${20+i*9}h38"/>\`).join('')}
</g>\`;
svg += \`<g transform="\${FRONT(20, 86, 132)}">
  <defs><clipPath id="isoScr"><rect x="10" y="10" width="104" height="58" rx="4"/></clipPath></defs>
  <rect class="face glass" x="10" y="10" width="104" height="58" rx="4"/>
  <g clip-path="url(#isoScr)">
    <text id="cabCage" class="lcd-dim" x="15" y="22" font-size="7.2">CAGE 0x2800_0000_0000</text>
    <text id="cabLock" class="lcd" x="15" y="35" font-size="8.5">LOCKER: THREAD #1</text>
    <text id="cabRealm" class="lcd-dim" x="15" y="48" font-size="7.5">REALMS: 1 · TASKS: 2</text>
    <text id="cabMsg" class="lcd" x="15" y="61" font-size="7.5">ISOLATE ENTERED</text>
  </g>
  <rect class="detail" x="10" y="76" width="104" height="28" rx="2"/>
  <path class="detail" d="M62 76v28"/>
  <circle class="struct" cx="55" cy="90" r="2.2"/>
  <circle class="struct" cx="69" cy="90" r="2.2"/>
</g>\`;

// 4. Back-right Twin Heap Reservation Vessels (Code-Range & Old/New Cage Silos)
svg += box(160, 22, 18, 72, 64, 98, 6);
svg += \`<g transform="\${TOP(160, 22, 116)}">
  <circle class="struct" cx="36" cy="32" r="20"/>
  <circle class="detail" cx="36" cy="32" r="11"/>
</g>\`;
svg += \`<g transform="\${FRONT(160, 86, 116)}">
  <rect class="face glass" x="28" y="10" width="16" height="58" rx="3"/>
  <rect id="tankBar1" fill="var(--live)" x="31" y="44" width="10" height="21" rx="1"/>
  <text class="lbl" x="36" y="78" font-size="6.6">HEAP 4G</text>
</g>\`;

svg += box(244, 22, 18, 70, 64, 82, 6);
svg += \`<g transform="\${TOP(244, 22, 100)}">
  <circle class="struct" cx="35" cy="32" r="18"/>
  <circle class="detail" cx="35" cy="32" r="9"/>
</g>\`;
svg += \`<g transform="\${FRONT(244, 86, 100)}">
  <rect class="face glass" x="27" y="10" width="16" height="46" rx="3"/>
  <rect id="tankBar2" fill="var(--live)" x="30" y="36" width="10" height="17" rx="1"/>
  <text class="lbl" x="35" y="66" font-size="6.6">REALMS</text>
</g>\`;

// 5. Middle Microtask Pump Manifold + 4 Queue Stage Cells (y = 104..146)
svg += box(156, 102, 18, 160, 42, 22, 4);
for (let i = 0; i < 4; i++) {
  const qx = 166 + i * 37;
  svg += \`<g class="unit" id="mtask\${i}">\${box(qx, 109, 40, 28, 28, 8, 2)}<g transform="\${TOP(qx, 109, 48)}"><text x="14" y="17" font-size="7.2" class="top-lbl">Q\${i+1}</text></g></g>\`;
}

// 6. Front Operator Control Pedestal (y = 152..198, completely clear of front corner guards)
svg += box(18, 152, 18, 272, 46, 14, 4);
const BTNS = [
  ['t1', 'LOCK T1', 24, 44, true],
  ['t2', 'LOCK T2', 73, 44, false],
  ['unlock', 'UNLOCK', 122, 42, false],
  ['realm', '+REALM', 169, 40, false],
  ['enq', '+TASK', 214, 34, false],
  ['drain', 'DRAIN', 253, 32, true]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 158, 32, bw, 30, 8, 3)}<g transform="\${TOP(bx, 158, 40)}"><text x="\${bw/2}" y="18.5" font-size="7">\${lbl}</text></g></g>\`;
});

// 7. Low front corner skid bumper bollards completing the 4 GiB cage perimeter
svg += box(6, 212, 18, 10, 10, 28, 2);
svg += box(324, 212, 18, 10, 10, 28, 2);

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = { owner: 1, realms: 1, tasks: 2, msg: 'ISOLATE ENTERED (T1)', blocked: false };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function render() {
  $('cabLock').textContent = st.owner ? 'LOCKER: THREAD #' + st.owner : 'LOCKER: UNLOCKED (IDLE)';
  $('cabRealm').textContent = 'REALMS: ' + st.realms + ' · QUEUE: ' + st.tasks + '/4';
  $('cabMsg').textContent = st.msg;
  const h1 = Math.min(50, 14 + st.realms * 8 + st.tasks * 3);
  $('tankBar1').setAttribute('y', String(65 - h1));
  $('tankBar1').setAttribute('height', String(h1));
  const h2 = Math.min(38, st.realms * 9);
  $('tankBar2').setAttribute('y', String(53 - h2));
  $('tankBar2').setAttribute('height', String(h2));

  for (let i = 0; i < 4; i++) {
    $('mtask' + i).classList.toggle('lit', i < st.tasks && st.owner !== 0);
    $('mtask' + i).classList.toggle('mid', i < st.tasks && st.owner === 0);
  }
  keys.get('t1').classList.toggle('sel', st.owner === 1);
  keys.get('t2').classList.toggle('sel', st.owner === 2);

  const lockStr = st.owner ? 'thread #' + st.owner + ' locked' : 'unlocked';
  $('readout').textContent = (st.blocked ? 'contended · ' : '') + lockStr + ' · ' + st.realms + (st.realms === 1 ? ' realm · ' : ' realms · ') + st.tasks + ' tasks';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  st.blocked = false;
  if (k === 't1' || k === 't2') {
    const want = k === 't1' ? 1 : 2;
    if (st.owner !== 0 && st.owner !== want) {
      st.blocked = true;
      st.msg = 'DENIED: T' + st.owner + ' HOLDS v8::Locker';
    } else {
      st.owner = want;
      st.msg = 'ISOLATE ENTERED (T' + want + ')';
    }
  } else if (k === 'unlock') {
    st.owner = 0;
    st.msg = 'EXITED ISOLATE · IDLE';
  } else if (k === 'realm') {
    if (!st.owner) { st.blocked = true; st.msg = 'LOCK THREAD BEFORE ALLOC'; }
    else { st.realms = (st.realms % 4) + 1; st.msg = 'NEW v8::Context #' + st.realms; }
  } else if (k === 'enq') {
    if (!st.owner) { st.blocked = true; st.msg = 'LOCK THREAD TO ENQUEUE'; }
    else if (st.tasks < 4) { st.tasks++; st.msg = 'ENQUEUED PROMISE JOB #' + st.tasks; }
    else st.msg = 'MICROTASK RING FULL (4/4)';
  } else if (k === 'drain') {
    if (!st.owner) { st.blocked = true; st.msg = 'LOCK THREAD TO DRAIN'; }
    else { const n = st.tasks; st.tasks = 0; st.msg = 'DRAINED ' + n + ' MICROTASKS'; }
  }
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { '1':'t1', '2':'t2', 'u':'unlock', 'r':'realm', 'm':'enq', 'd':'drain', ' ':'drain' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });

  // ==========================================================================
  // FIG 2: Pointer Tagging (Smi vs. HeapObject) — Carrier Stamp vs. RFID Pallet
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-02-pointer-tagging",
    fig: "Fig 2",
    title: "Pointer Tagging · Carrier Stamp vs. RFID Pallet",
    hint: "toggle bit 0 · stamp smi or deref rfid",
    initialReadout: "smi · 0x00000054 (bit0=0) · val 42 · 0 derefs",
    ariaLabel:
      "Isometric pointer-tagging roller conveyor station with overhead bit-0 laser scanner gantry, carrier pallet switching between an on-carrier stamped Smi casting and an RFID manifest linked to a rear HeapObject bay.",
    footHelp:
      "Keys: <kbd>S</kbd> stamp immediate Smi (<kbd>bit0=0</kbd>) · <kbd>D</kbd> double Smi (<kbd>&lt;&lt;1</kbd>) · <kbd>H</kbd> RFID HeapObject pallet (<kbd>bit0=1</kbd>) · <kbd>F</kbd> mutate heap field · <kbd>N</kbd> advance carrier.",
    bounds: [
      [0, 0, 0, 390, 214, 120],
    ],
    sceneJs: `
let svg = '';
// 1. Rear Off-Belt Heap Storage Vault (only touched when bit0 == 1!)
svg += box(210, 0, 0, 174, 56, 96, 5);
svg += \`<g transform="\${FRONT(210, 56, 96)}">
  <defs><clipPath id="ptScr"><rect x="10" y="9" width="154" height="52" rx="4"/></clipPath></defs>
  <rect class="face glass" x="10" y="9" width="154" height="52" rx="4"/>
  <g clip-path="url(#ptScr)">
    <text id="ptWord" class="lcd" x="16" y="22" font-size="8.5">WORD: 0x0000_0054 [bit0=0]</text>
    <text id="ptKind" class="lcd-dim" x="16" y="35" font-size="8">KIND: 31-BIT IMMEDIATE SMI</text>
    <text id="ptTarget" class="lcd" x="16" y="49" font-size="8.2">CARRIER VALUE = 42 (0 HOPS)</text>
  </g>
  <text class="lbl" x="87" y="69" font-size="6.8">COMPRESSED HEAP BAY [0x0018_4200]</text>
</g>\`;
// Physical HeapObject Cell sitting on top of the rear Heap Vault
svg += \`<g class="unit" id="heapVaultCell">\${box(254, 10, 96, 88, 36, 16, 3)}<g transform="\${TOP(254, 10, 112)}"><text id="heapVaultTxt" x="44" y="21" font-size="7.6" class="top-lbl">IDLE (UNREAD)</text></g></g>\`;

// 2. Three Conveyor Trestle Legs + Long Roller-Conveyor Transfer Bed (y = 70..154)
[22, 176, 330].forEach(lx => { svg += box(lx, 74, 0, 26, 72, 18, 2); });
svg += box(0, 68, 18, 386, 84, 14, 4);
// 17 transverse steel conveyor rollers on TOP
svg += \`<g transform="\${TOP(0, 68, 32)}">
  \${Array.from({length:17},(_,i)=>\`<rect class="detail" x="\${12+i*22}" y="6" width="14" height="72" rx="3"/>\`).join('')}
</g>\`;

// 3. Back Post of Bit-0 Laser Scanner Gantry (x = 136, y = 58)
svg += box(136, 58, 0, 18, 12, 104, 2);

// 4. Moving Carrier Pallet in Inspection Zone (id="carrierGroup")
svg += \`<g class="unit" id="carrierGroup">
  \${box(144, 78, 32, 98, 64, 8, 3)}
  <!-- On-carrier Raised Stamped Metal Casting (shown for Smi bit0=0) -->
  <g id="smiPart">
    \${box(160, 90, 40, 66, 40, 18, 4)}
    <g transform="\${TOP(160, 90, 58)}"><text id="smiStampTxt" x="33" y="24" font-size="11" class="top-lbl">#42</text></g>
  </g>
  <!-- Flat RFID Pallet Manifest Card (shown for HeapObject bit0=1) -->
  <g id="rfidPart" style="display:none">
    \${box(156, 88, 40, 74, 44, 3, 2)}
    <g transform="\${TOP(156, 88, 43)}">
      <rect class="struct" x="6" y="6" width="62" height="32" rx="2"/>
      <path class="detail" d="M12 14h28M12 21h42M12 28h34"/>
      <text x="54" y="17" font-size="7.5" class="lcd">…01</text>
    </g>
  </g>
</g>\`;

// 5. Front Post & Overhead Cross-Arm of Bit-0 Laser Gantry (painted AFTER carrier for true occlusion!)
svg += box(136, 150, 0, 18, 12, 104, 2);
svg += box(132, 56, 104, 26, 108, 12, 3);
svg += \`<g transform="\${FRONT(132, 164, 116)}"><text class="lbl-hi" x="13" y="9" font-size="6.5">BIT0</text></g>\`;

// 6. Front Control Rail (y = 168..210)
svg += box(18, 168, 0, 350, 44, 12, 4);
const BTNS = [
  ['smi', 'SMI (…0)', 28, 62, true],
  ['shl', 'SMI × 2', 96, 56, false],
  ['heap', 'RFID (…1)', 158, 66, true],
  ['field', '+FIELD', 230, 56, false],
  ['next', 'ADVANCE', 292, 66, false]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 174, 12, bw, 32, 8, 3)}<g transform="\${TOP(bx, 174, 20)}"><text x="\${bw/2}" y="19.5" font-size="8.2">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = { isHeap: false, smiVal: 42, propVal: 108, slotOffset: 0 };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function render() {
  const cg = $('carrierGroup');
  cg.style.transform = \`translate(\${st.slotOffset * 14}px, \${st.slotOffset * 8}px)\`;
  $('smiPart').style.display = st.isHeap ? 'none' : '';
  $('rfidPart').style.display = st.isHeap ? '' : 'none';
  cg.classList.toggle('lit', !st.isHeap);
  $('heapVaultCell').classList.toggle('lit', st.isHeap);

  if (!st.isHeap) {
    const raw = ((st.smiVal << 1) >>> 0).toString(16).toUpperCase().padStart(8, '0');
    $('smiStampTxt').textContent = '#' + st.smiVal;
    $('ptWord').textContent = 'WORD: 0x' + raw + ' [bit0 = 0]';
    $('ptKind').textContent = 'KIND: ON-CARRIER 31-BIT SMI';
    $('ptTarget').textContent = 'IMMEDIATE = ' + st.smiVal + ' (0 HEAP HOPS)';
    $('heapVaultTxt').textContent = 'BYPASSED (0 READS)';
    $('readout').textContent = 'smi · 0x' + raw.toLowerCase() + ' (bit0=0) · val ' + st.smiVal + ' · 0 derefs';
  } else {
    const addr = (0x00184201 + st.slotOffset * 16) >>> 0;
    const hex = addr.toString(16).toUpperCase().padStart(8, '0');
    $('ptWord').textContent = 'WORD: 0x' + hex + ' [bit0 = 1]';
    $('ptKind').textContent = 'KIND: RFID HEAPOBJECT MANIFEST';
    $('ptTarget').textContent = 'DEREF [addr-1] -> {x: ' + st.propVal + '}';
    $('heapVaultTxt').textContent = 'MAP#1 {x:' + st.propVal + '}';
    $('readout').textContent = 'heapobj · 0x' + hex.toLowerCase() + ' (bit0=1) · {x:' + st.propVal + '} · 1 deref';
  }
  keys.get('smi').classList.toggle('sel', !st.isHeap);
  keys.get('heap').classList.toggle('sel', st.isHeap);
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'smi') st.isHeap = false;
  else if (k === 'shl') { st.isHeap = false; st.smiVal = st.smiVal >= 512 ? 7 : st.smiVal * 2; }
  else if (k === 'heap') st.isHeap = true;
  else if (k === 'field') { st.isHeap = true; st.propVal += 12; }
  else if (k === 'next') { st.slotOffset = ((st.slotOffset + 2) % 3) - 1; st.smiVal = st.smiVal === 42 ? 99 : 42; }
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { 's':'smi', 'd':'shl', 'h':'heap', 'f':'field', 'n':'next', ' ':'heap' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });

  // ==========================================================================
  // FIG 3: Hidden Classes (Map) & Transitions — Automated Turret Punch Press
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-03-hidden-classes",
    fig: "Fig 3",
    title: "Hidden Classes · Turret Punch & Indexed Dies",
    hint: "punch fields · index map dies · test delete",
    initialReadout: "map#2 {x@+4, y@+8} · die #2 · fast in-object",
    ariaLabel:
      "Isometric automated turret punch press representing V8 HiddenClasses and Map transitions, with overhanging C-frame ram, rotary 4-die indexing turret, and front X-Y sheet clamp punching in-object property slots.",
    footHelp:
      "Keys: <kbd>X</kbd> punch <code>+x (@+4)</code> · <kbd>Y</kbd> punch <code>+y (@+8)</code> · <kbd>Z</kbd> punch <code>+z (@+12)</code> · <kbd>D</kbd> delete property (degrades to dictionary mode) · <kbd>N</kbd> fresh JSObject blank.",
    bounds: [
      [0, 0, 0, 344, 236, 162],
    ],
    sceneJs: `
let svg = '';
// 1. Heavy Punch Press Bed (340 x 228 x 20)
svg += box(0, 8, 0, 340, 224, 20, 5);
// 2. Rear C-Frame Throat Column (x = 74, y = 0, z = 20..152)
svg += box(74, 0, 20, 118, 62, 132, 5);
svg += \`<g transform="\${SIDE(192, 62, 152)}">
  \${Array.from({length:7},(_,i)=>\`<path class="detail" d="M12 \${22+i*12}h38"/>\`).join('')}
</g>\`;

// 3. Right Transition-Tree Readout Wing (x = 212, y = 14, z = 20..112)
svg += box(212, 14, 20, 116, 56, 92, 5);
svg += \`<g transform="\${FRONT(212, 70, 112)}">
  <defs><clipPath id="mapScr"><rect x="8" y="8" width="100" height="58" rx="4"/></clipPath></defs>
  <rect class="face glass" x="8" y="8" width="100" height="58" rx="4"/>
  <g clip-path="url(#mapScr)">
    <text id="mpHead" class="lcd" x="12" y="21" font-size="7.2">MAP#2 [FAST SLOTS]</text>
    <text id="mpTree" class="lcd-dim" x="13" y="34" font-size="7.5">M0 -&gt; +x@4 -&gt; +y@8</text>
    <text id="mpWord" class="lcd" x="13" y="48" font-size="7.8">HDR[0] = Map(0x0281)</text>
    <text id="mpMode" class="lcd-dim" x="13" y="60" font-size="7.2">DESC ARRAY: 2 ENTRIES</text>
  </g>
</g>\`;

// 4. Rotary Indexed Die Turret Platter (x = 58, y = 66, z = 20..36)
svg += box(58, 66, 20, 150, 82, 16, 14);
svg += \`<g transform="\${TOP(58, 66, 36)}">
  <ellipse class="struct" cx="75" cy="41" rx="64" ry="34"/>
  <ellipse class="detail" cx="75" cy="41" rx="26" ry="14"/>
  <path class="detail" d="M11 41h128M75 7v68"/>
</g>\`;

// 4 Indexed Hardened Die Stations around the turret (M0, +x, +y, +z)
const DIES = [
  ['die0', 'M0', 72, 74],
  ['die1', '+x', 152, 74],
  ['die2', '+y', 72, 112],
  ['die3', '+z', 152, 112]
];
DIES.forEach(([id, lbl, dx, dy]) => {
  svg += \`<g class="unit" id="\${id}">\${box(dx, dy, 36, 36, 24, 11, 4)}<g transform="\${TOP(dx, dy, 47)}"><text x="18" y="15" font-size="8" class="top-lbl">\${lbl}</text></g></g>\`;
});

// 5. Overhanging Cantilevered Ram Head + Moving Striker Cylinder (painted AFTER turret!)
svg += \`<g class="unit" id="punchRam">\${box(116, 86, 86, 34, 30, 30, 4)}</g>\`;
svg += box(74, 0, 114, 118, 134, 42, 5);
svg += \`<g transform="\${FRONT(74, 134, 156)}">
  <rect class="detail" x="12" y="10" width="94" height="22" rx="3"/>
  <text class="lbl-hi" x="59" y="24" font-size="8.5">TURRET INDEXER · 20T</text>
</g>\`;

// 6. Front X-Y Sheet-Clamp Worktable & Punched JSObject Blank (y = 152..184)
svg += box(26, 152, 20, 288, 32, 6, 2);
svg += \`<g transform="\${TOP(26, 152, 26)}">
  <!-- JSObject Metal Sheet Blank with Map word + 3 punchable in-object property slots -->
  <rect class="face" x="16" y="4" width="256" height="24" rx="2"/>
  <rect fill="var(--live)" x="22" y="7" width="52" height="18" rx="1.5"/>
  <text fill="var(--ko-ink)" x="48" y="19" font-size="7.8" text-anchor="middle" font-family="var(--mono)" id="sheetMapLbl">MAP#2</text>
  <rect id="slotBox1" class="face glass" x="82" y="7" width="56" height="18" rx="1.5"/>
  <text id="slotTxt1" class="lcd" x="110" y="19" font-size="7.5" text-anchor="middle">+4: x</text>
  <rect id="slotBox2" class="face glass" x="146" y="7" width="56" height="18" rx="1.5"/>
  <text id="slotTxt2" class="lcd" x="174" y="19" font-size="7.5" text-anchor="middle">+8: y</text>
  <rect id="slotBox3" class="face glass" x="210" y="7" width="56" height="18" rx="1.5"/>
  <text id="slotTxt3" class="lcd-dim" x="238" y="19" font-size="7.5" text-anchor="middle">unpunched</text>
</g>\`;

// 7. Front Press Controls (y = 190..226)
const BTNS = [
  ['x', 'PUNCH +x', 24, 58, true],
  ['y', 'PUNCH +y', 88, 58, true],
  ['z', 'PUNCH +z', 152, 58, true],
  ['del', 'DELETE (DICT)', 216, 70, false],
  ['new', 'NEW', 292, 36, false]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 190, 20, bw, 30, 8, 3)}<g transform="\${TOP(bx, 190, 28)}"><text x="\${bw/2}" y="19" font-size="7.6">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = { props: ['x', 'y'], dict: false };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function strikeRam() {
  const ram = $('punchRam');
  ram.style.transform = 'translateY(8px)';
  ram.classList.add('lit');
  setTimeout(() => { ram.style.transform = ''; ram.classList.remove('lit'); }, 140);
}

function render() {
  const n = st.props.length;
  const activeDie = st.dict ? -1 : n;
  for (let i = 0; i < 4; i++) $('die' + i).classList.toggle('lit', i === activeDie);

  if (st.dict) {
    $('mpHead').textContent = 'DICT MODE [SLOW HASH]';
    $('mpTree').textContent = 'TRANSITION BROKEN (delete)';
    $('mpWord').textContent = 'HDR[0] = DictMap(0x09F1)';
    $('mpMode').textContent = 'NAME DICTIONARY BUCKETS';
    $('sheetMapLbl').textContent = 'DICT';
  } else {
    const chain = ['M0', ...st.props.map((p, i) => '+' + p + '@' + ((i + 1) * 4))].join(' -> ');
    $('mpHead').textContent = 'MAP#' + n + ' [FAST SLOTS]';
    $('mpTree').textContent = chain;
    $('mpWord').textContent = 'HDR[0] = Map(0x028' + n + ')';
    $('mpMode').textContent = 'DESC ARRAY: ' + n + (n === 1 ? ' ENTRY' : ' ENTRIES');
    $('sheetMapLbl').textContent = 'MAP#' + n;
  }

  [1, 2, 3].forEach(idx => {
    const p = st.props[idx - 1];
    const txt = $('slotTxt' + idx);
    if (st.dict) {
      txt.textContent = p ? ('hash:' + p) : 'hole';
      txt.setAttribute('class', p ? 'lcd' : 'lcd-dim');
    } else if (p) {
      txt.textContent = '+' + (idx * 4) + ': ' + p;
      txt.setAttribute('class', 'lcd');
    } else {
      txt.textContent = 'blank';
      txt.setAttribute('class', 'lcd-dim');
    }
  });

  $('readout').textContent = st.dict
    ? 'dictionary map · slow hash table · ' + n + ' props'
    : 'map#' + n + ' {' + (st.props.map((p, i) => p + '@+' + ((i + 1) * 4)).join(', ') || 'empty') + '} · die #' + n;
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'new') { st.props = []; st.dict = false; strikeRam(); }
  else if (k === 'del') { st.props.pop(); st.dict = true; strikeRam(); }
  else if (['x', 'y', 'z'].includes(k)) {
    if (!st.props.includes(k) && st.props.length < 3) { st.props.push(k); strikeRam(); }
  }
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { 'x':'x', 'y':'y', 'z':'z', 'd':'del', 'Backspace':'del', 'n':'new', 'Escape':'new' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });

  // ==========================================================================
  // FIG 4: Parser & Pre-Parser — Vibration Feeder Bowl & Optical Sorting Gate
  // ==========================================================================
  writeIsoFigure({
    slug: "fig-04-parser",
    fig: "Fig 4",
    title: "Parser & Pre-Parser · Vibration Bowl & Optical Gate",
    hint: "vibrate utf-16 bowl · sort ast vs scopeinfo",
    initialReadout: "lazy preparse · 3 scopeinfo / 2 ast · 68 tok",
    ariaLabel:
      "Isometric vibration feeder bowl shaking UTF-16 tokens along a linear optical sorting chute that diverts cold functions into a ScopeInfo bin and eager functions into a full AST bin.",
    footHelp:
      "Keys: <kbd>C</kbd> feed cold inner function (<kbd>ScopeInfo</kbd>) · <kbd>H</kbd> feed hot eager IIFE (<kbd>AST</kbd>) · <kbd>A</kbd> feed arrow closure · <kbd>E</kbd> inject early syntax error · <kbd>Esc</kbd> empty bins.",
    bounds: [
      [0, 0, 0, 384, 224, 118],
    ],
    sceneJs: `
let svg = '';
// 1. Machine Base Slab (380 x 220 x 14)
svg += box(0, 0, 0, 380, 220, 14, 5);

// 2. Back-Right Full AST Collection Hopper Bin (eager parse output, y = 16..84)
svg += box(256, 16, 14, 112, 68, 56, 4);
svg += \`<g transform="\${TOP(256, 16, 70)}">
  <rect class="face glass" x="8" y="8" width="96" height="52" rx="3"/>
  <text id="astBinTop" class="lcd" x="56" y="38" font-size="11" text-anchor="middle">2 AST TREES</text>
</g>\`;
svg += \`<g transform="\${FRONT(256, 84, 70)}"><text class="lbl-hi" x="56" y="32" font-size="8">EAGER AST BIN</text></g>\`;

// 3. Left Concentric Stepped Vibration Feeder Bowl (id="vibBowl", x = 16..140, y = 28..152)
svg += box(24, 36, 14, 108, 108, 18, 6); // heavy electromagnetic base
svg += \`<g class="unit" id="vibBowl">
  \${box(16, 28, 32, 124, 124, 20, 8)}
  \${box(26, 38, 52, 104, 104, 18, 7)}
  \${box(38, 50, 70, 80, 80, 14, 6)}
  <g transform="\${TOP(38, 50, 84)}">
    <circle class="struct" cx="40" cy="40" r="34"/>
    <circle class="detail" cx="40" cy="40" r="23"/>
    <circle class="detail" cx="40" cy="40" r="12"/>
    <rect fill="var(--live)" x="22" y="32" width="10" height="6" rx="1"/>
    <rect fill="var(--live)" x="46" y="20" width="12" height="6" rx="1"/>
    <rect fill="var(--live)" x="48" y="50" width="10" height="6" rx="1"/>
    <text class="lbl" x="40" y="43" font-size="6.8">UTF-16</text>
  </g>
</g>\`;

// 4. Linear Vibratory Feed Chute + Optical Sorting Gate Housing (x = 136..252, y = 66..108)
svg += box(150, 74, 14, 86, 28, 38, 2); // chute pedestal
svg += box(136, 68, 52, 118, 38, 12, 3); // vibratory track
// Pivoting Optical Diverter Gate Vane on track
svg += \`<g class="unit lit" id="diverterGate">\${box(224, 74, 64, 26, 10, 10, 2)}</g>\`;
// Overhead Optical Scanner Arch spanning the track
svg += box(172, 62, 64, 52, 50, 44, 4);
svg += \`<g transform="\${FRONT(172, 112, 108)}">
  <rect class="face glass" x="6" y="6" width="40" height="32" rx="3"/>
  <text id="optMode" class="lcd" x="26" y="19" font-size="7.2" text-anchor="middle">LAZY</text>
  <text id="optTok" class="lcd-dim" x="26" y="31" font-size="6.8" text-anchor="middle">fn inner()</text>
</g>\`;

// 5. Front-Right Fast ScopeInfo Hopper Bin (Pre-Parser output, y = 98..164)
svg += box(256, 98, 14, 112, 66, 44, 4);
svg += \`<g transform="\${TOP(256, 98, 58)}">
  <rect class="face glass" x="8" y="8" width="96" height="50" rx="3"/>
  <text id="scopeBinTop" class="lcd" x="56" y="36" font-size="10.5" text-anchor="middle">3 SCOPEINFO</text>
</g>\`;
svg += \`<g transform="\${FRONT(256, 164, 58)}"><text class="lbl-hi" x="56" y="26" font-size="7.8">PRE-PARSER BIN</text></g>\`;

// 6. Front Control Bar (y = 174..212)
const BTNS = [
  ['cold', 'COLD FN', 18, 66, false],
  ['hot', 'HOT IIFE', 90, 68, true],
  ['arrow', 'ARROW =>', 164, 68, false],
  ['err', 'EARLY ERR', 238, 70, false],
  ['clr', 'EMPTY', 314, 50, false]
];
BTNS.forEach(([id, lbl, bx, bw, op]) => {
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(bx, 176, 14, bw, 32, 8, 3)}<g transform="\${TOP(bx, 176, 22)}"><text x="\${bw/2}" y="19.5" font-size="7.8">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = { scopeCount: 3, astCount: 2, tokens: 68, gate: 'lazy', tokLabel: 'fn inner()', err: false };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(k => [k.dataset.k, k]));

function shakeBowl() {
  const b = $('vibBowl');
  b.style.transform = 'translate(3px, -2px)';
  setTimeout(() => { b.style.transform = 'translate(-2px, 1px)'; }, 55);
  setTimeout(() => { b.style.transform = ''; }, 115);
}

function render() {
  $('optMode').textContent = st.err ? 'SYNTAX!' : st.gate.toUpperCase();
  $('optTok').textContent = st.tokLabel;
  $('astBinTop').textContent = st.astCount + (st.astCount === 1 ? ' AST TREE' : ' AST TREES');
  $('scopeBinTop').textContent = st.scopeCount + ' SCOPEINFO';
  const gateEl = $('diverterGate');
  gateEl.style.transform = st.gate === 'eager' ? 'translate(-4px, -6px)' : 'translate(4px, 6px)';
  gateEl.classList.toggle('lit', !st.err);

  $('readout').textContent = st.err
    ? 'early syntax error · rejected at gate · ' + st.tokens + ' tok'
    : st.gate + ' sort · ' + st.scopeCount + ' scopeinfo / ' + st.astCount + ' ast · ' + st.tokens + ' tok';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  shakeBowl();
  st.err = false;
  if (k === 'cold') { st.scopeCount++; st.tokens += 16; st.gate = 'lazy'; st.tokLabel = 'fn cold(){…}'; }
  else if (k === 'hot') { st.astCount++; st.tokens += 14; st.gate = 'eager'; st.tokLabel = '(function(){})()'; }
  else if (k === 'arrow') { st.scopeCount++; st.tokens += 9; st.gate = 'lazy'; st.tokLabel = 'x => x + 1'; }
  else if (k === 'err') { st.err = true; st.tokens += 5; st.tokLabel = 'let x; let x;'; }
  else if (k === 'clr') { st.scopeCount = 0; st.astCount = 0; st.tokens = 0; st.gate = 'ready'; st.tokLabel = 'empty bowl'; }
  render();
}

stage.addEventListener('pointerdown', e => { const el = e.target.closest('.press'); if (el) { e.preventDefault(); act(el.dataset.k); } });
const KM = { 'c':'cold', 'h':'hot', 'a':'arrow', 'e':'err', 'Escape':'clr', ' ':'hot' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KM[e.key] || KM[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
  });
}
