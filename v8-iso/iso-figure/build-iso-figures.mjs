import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const PAGES_DIR = join(dirname(fileURLToPath(import.meta.url)), "..", "pages");
mkdirSync(PAGES_DIR, { recursive: true });

// Shared CSS & frame strictly following MrBongoC/ai-iso-skill (skills/iso-figure/SKILL.md)
function makeIsoPage({ slug, fig, title, hint, initialReadout, viewBox, ariaLabel, footHelp, extraCss = "", scriptBody }) {
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${fig} — ${title}</title>
<style>
  :root {
    color-scheme: dark;
    --bg:#0c0d0e; --panel:#141516; --edge:#222426;
    --line:#3d4144; --detail:#2b2e30; --body:#17181a; --deck:#1b1d1f;
    --ink:#868b8f; --ink-hi:#e6e8e9; --live:#f4f5f5;
    --kn:#232629; --kn-line:#565b5f; --ko:#d9dcde; --ko-line:#5a5f63; --ko-ink:#141618;
    --glass:#0a0b0c;
    --mono:"JetBrains Mono","SF Mono",ui-monospace,Menlo,Consolas,monospace;
  }
  @media (prefers-color-scheme: light) { :root:not([data-theme="dark"]) {
    color-scheme: light;
    --bg:#e9eaea; --panel:#f6f6f5; --edge:#d6d8d8;
    --line:#8e9397; --detail:#c3c6c8; --body:#ececeb; --deck:#f3f3f2;
    --ink:#5f6468; --ink-hi:#16181a; --live:#0c0d0e;
    --kn:#ffffff; --kn-line:#7b8084; --ko:#26282a; --ko-line:#0c0d0e; --ko-ink:#f4f5f5;
    --glass:#e2e4e4;
  } }
  :root[data-theme="light"] {
    color-scheme: light;
    --bg:#e9eaea; --panel:#f6f6f5; --edge:#d6d8d8;
    --line:#8e9397; --detail:#c3c6c8; --body:#ececeb; --deck:#f3f3f2;
    --ink:#5f6468; --ink-hi:#16181a; --live:#0c0d0e;
    --kn:#ffffff; --kn-line:#7b8084; --ko:#26282a; --ko-line:#0c0d0e; --ko-ink:#f4f5f5;
    --glass:#e2e4e4;
  }
  * { box-sizing:border-box; }
  body { margin:0; background:var(--bg); color:var(--ink); font-family:var(--mono); font-size:13px; padding:20px 16px; }
  html[data-embed="1"] body { background:transparent; padding:0; }
  html[data-embed="1"] main { max-width:none; }
  html[data-embed="1"] .foot-help { display:none; }
  html[data-compact="1"] figure { padding:12px 14px; border-radius:10px; }
  html[data-compact="1"] .cap { font-size:10.5px; letter-spacing:.09em; }
  main { max-width:760px; margin-inline:auto; display:grid; gap:12px; }
  figure { margin:0; background:var(--panel); border:1px solid var(--edge); border-radius:16px; padding:18px 22px; display:grid; gap:6px; }
  .cap { display:flex; flex-wrap:wrap; justify-content:space-between; align-items:baseline; gap:4px 14px; font-size:12px; text-transform:uppercase; letter-spacing:.12em; }
  .cap .hi { color:var(--ink-hi); text-transform:none; letter-spacing:.04em; }
  svg { width:100%; height:auto; display:block; touch-action:manipulation; user-select:none; -webkit-user-select:none; }
  svg:focus-visible { outline:2px solid var(--live); outline-offset:4px; border-radius:8px; }
  .face { fill:var(--body); stroke:var(--line); stroke-width:1; vector-effect:non-scaling-stroke; stroke-linejoin:round; }
  .face.top { fill:var(--deck); }
  .detail { fill:none; stroke:var(--detail); stroke-width:1; vector-effect:non-scaling-stroke; }
  .glass { fill:var(--glass); }
  .lcd { fill:var(--live); font-family:var(--mono); }
  .lcd-dim { fill:var(--ink); font-family:var(--mono); }
  .trace { fill:none; stroke:var(--live); stroke-width:1.3; vector-effect:non-scaling-stroke; stroke-linejoin:round; }
  .press { cursor:pointer; transition:transform 60ms ease-out; }
  .press .face { fill:var(--kn); stroke:var(--kn-line); transition:stroke 90ms; }
  .press.op .face { fill:var(--ko); stroke:var(--ko-line); }
  .press text { fill:var(--ink-hi); font-family:var(--mono); text-anchor:middle; pointer-events:none; }
  .press.op text { fill:var(--ko-ink); }
  .press.down { transform:translateY(4px); }
  .press.down .face, .press:hover .face.top, .press.sel .face { stroke:var(--live); }
  .press.sel text { fill:var(--live); }
  .press.op.sel text { fill:var(--ko-ink); }
  .cell .face { transition:fill 120ms, stroke 120ms; }
  .cell.lit .face { stroke:var(--live); }
  .cell.lit .face.top { fill:var(--ko); }
  .cell.mid .face { stroke:var(--kn-line); }
  .foot-help { margin:0; max-width:66ch; line-height:1.6; font-size:12px; }
  kbd { font:inherit; color:var(--ink-hi); border:1px solid var(--edge); border-radius:4px; padding:0 4px; }
  @media (prefers-reduced-motion:reduce){ .press, .cell .face { transition:none; } }
  ${extraCss}
</style>
</head>
<body>
<main>
  <figure class="iso-plate">
    <div class="cap"><span class="hi">${fig}</span><span>${title}</span></div>
    <svg id="stage" viewBox="${viewBox}" tabindex="0" role="img" aria-label="${ariaLabel}"></svg>
    <div class="cap"><span>${hint}</span><span class="hi" id="readout" data-readout>${initialReadout}</span></div>
  </figure>
  <p class="foot-help">${footHelp}</p>
</main>
<script>
(() => {
  const params = new URLSearchParams(location.search);
  if (params.get("embed") === "1") document.documentElement.setAttribute("data-embed", "1");
  if (params.get("compact") === "1") document.documentElement.setAttribute("data-compact", "1");
  const qt = params.get("theme");
  if (qt === "light" || qt === "dark") document.documentElement.setAttribute("data-theme", qt);
  else document.documentElement.setAttribute("data-theme", "dark");
  window.addEventListener("message", (ev) => {
    if (ev.data && ev.data.type === "v8-iso-theme" && (ev.data.theme === "light" || ev.data.theme === "dark")) {
      document.documentElement.setAttribute("data-theme", ev.data.theme);
    }
  });
  if (params.get("embed") === "1" && window.parent && window.parent !== window) {
    const postH = () => {
      const f = document.querySelector("figure");
      if (f) window.parent.postMessage({ type: "v8-iso-height", id: params.get("id") || "${slug}", height: Math.ceil(f.getBoundingClientRect().height) }, "*");
    };
    new ResizeObserver(postH).observe(document.body);
    window.addEventListener("load", postH);
    setTimeout(postH, 60);
  }
})();
${scriptBody}
</script>
</body>
</html>`;
}

// ============================================================================
// 1B: V8 Scanner & Lazy/Eager AST Desk Console
// ============================================================================
const page01 = makeIsoPage({
  slug: "iso-01-parser",
  fig: "Fig 1B",
  title: "V8 Token & AST Desk Console",
  hint: "press tokens · toggle lazy/eager",
  initialReadout: "eager · 5 tok · 4 ast",
  viewBox: "0 0 610 382",
  ariaLabel: "Isometric V8 lexer and parser console. Press token keys or type 1-8, M to toggle PreParser vs Eager AST, Backspace, or Escape.",
  footHelp: "Keys: <kbd>1</kbd> fn <kbd>2</kbd> (x) <kbd>3</kbd> =&gt; <kbd>4</kbd> x <kbd>5</kbd> + <kbd>6</kbd> * <kbd>7</kbd> 2 <kbd>8</kbd> {ret} · <kbd>M</kbd> lazy/eager · <kbd>Backspace</kbd> pop · <kbd>Esc</kbd> clear.",
  scriptBody: `
// ---- iso kernel (verbatim MrBongoC/ai-iso-skill) ----
const C = Math.cos(Math.PI/6), S = Math.sin(Math.PI/6), OX = 248, OY = 96;
const P = (x,y,z) => [(x-y)*C + OX, (x+y)*S - z + OY];
const D = (x,y,z) => [(x-y)*C, (x+y)*S - z];
const plane = (O,U,V) => { const o=P(...O), u=D(...U), v=D(...V); return \`matrix(\${u[0]} \${u[1]} \${v[0]} \${v[1]} \${o[0]} \${o[1]})\`; };
const TOP = (x,y,z) => plane([x,y,z],[1,0,0],[0,1,0]);
const FRONT = (x,y,z) => plane([x,y,z],[1,0,0],[0,0,-1]);
const SIDE = (x,y,z) => plane([x,y,z],[0,-1,0],[0,0,-1]);
const rect = (t,w,h,r=0,cls='face') => \`<g transform="\${t}"><rect class="\${cls}" width="\${w}" height="\${h}" rx="\${r}"/></g>\`;
const box = (x,y,z,w,d,h,r=0) => rect(SIDE(x+w,y+d,z+h),d,h,Math.min(r,h/4)) + rect(FRONT(x,y+d,z+h),w,h,Math.min(r,h/4)) + rect(TOP(x,y,z+h),w,d,r,'face top');

// ---- scene back-to-front ----
const W = 340, DECK = 20, RH = 68;
let svg = box(0,0,0, W,210,DECK, 8);
svg += box(0,0,DECK, W,62,RH, 6);
// Top cooling slits on riser
svg += \`<g transform="\${TOP(0,0,DECK+RH)}">\${Array.from({length:12},(_,i)=>\`<rect class="detail" x="\${24+i*24}" y="12" width="14" height="5" rx="2"/>\`).join('')}</g>\`;
// Front CRT screen with clipPath
svg += \`<g transform="\${FRONT(0,62,DECK+RH)}">
  <defs><clipPath id="scr1"><rect x="16" y="8" width="238" height="50" rx="5"/></clipPath></defs>
  <rect class="face glass" x="16" y="8" width="238" height="50" rx="5"/>
  <g clip-path="url(#scr1)">
    <text id="scrMode" class="lcd-dim" x="24" y="21" font-size="8.5">MODE: EAGER PARSER</text>
    <text id="scrSrc" class="lcd" x="24" y="36" font-size="11.5">(x) =&gt; x + 2</text>
    <text id="scrAst" class="lcd-dim" x="24" y="50" font-size="8.5">AST: ArrowFn &gt; BinOp(+)</text>
  </g>
  \${Array.from({length:7},(_,i)=>\`<path class="detail" d="M\${270+i*8} 12v42"/>\`).join('')}
</g>\`;

// Mode row (y = 74)
const MODES = [['mode','EAGER','m'],['pop','DEL','Backspace'],['clr','CLR','Escape']];
MODES.forEach(([id,lbl],i) => {
  const x = 18 + i*64 + (i===0 ? 0 : 12);
  svg += \`<g class="press\${id==='mode'?' op':''}" data-k="\${id}">\${box(x,74,DECK, id==='mode'?68:52,24,6, 3)}<g transform="\${TOP(x,74,DECK+6)}"><text x="\${id==='mode'?34:26}" y="15.5" font-size="9.5">\${lbl}</text></g></g>\`;
});

// Token grid (2 rows x 4 cols, y = 112 and y = 156)
const TOKS = [
  [['fn','fn','1'],['(x)','(x)','2'],['=>','=>','3'],['{ret}','{ret}','8']],
  [['x','x','4'],['+','+','5'],['*','*','6'],['2','2','7']]
];
TOKS.forEach((row,r) => row.forEach(([id,lbl],c) => {
  const x = 18 + c*78, y = 112 + r*42;
  const op = id === '=>' || id === '+' || id === '*';
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(x,y,DECK, 68,32,8, 4)}<g transform="\${TOP(x,y,DECK+8)}"><text x="34" y="20" font-size="12">\${lbl.replace('>','&gt;')}</text></g></g>\`;
}));

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const state = { eager: true, toks: ['(x)', '=>', 'x', '+', '2'] };
function analyze(toks, eager) {
  if (!toks.length) return { ast: 0, skipped: 0, tree: 'Empty Program' };
  const hasFn = toks.includes('fn') || toks.includes('=>') || toks.includes('{ret}');
  let nodes = 1; // Program
  const parts = [];
  if (toks.includes('fn')) { nodes += 2; parts.push('FnDecl'); }
  if (toks.includes('=>')) { nodes += 2; parts.push('ArrowFn'); }
  if (toks.includes('{ret}')) { nodes += 1; parts.push('Block'); }
  const ops = toks.filter(t => t === '+' || t === '*').length;
  const ids = toks.filter(t => t === 'x' || t === '2').length;
  if (!eager && hasFn) {
    const skipped = ops + ids + (toks.includes('{ret}') ? 1 : 0);
    return { ast: Math.max(1, parts.length ? 2 : 1), skipped, tree: 'ScopeShell (skipped ' + skipped + ' tok)' };
  }
  nodes += ops + ids;
  if (ops > 0) parts.push('BinOp(' + toks.filter(t => t === '+' || t === '*').join(',') + ')');
  else if (ids > 0) parts.push('Ident(' + ids + ')');
  return { ast: nodes, skipped: 0, tree: parts.join(' > ') || 'ExprStmt' };
}

const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(el => [el.dataset.k, el]));

function render() {
  const res = analyze(state.toks, state.eager);
  $('scrMode').textContent = state.eager ? 'MODE: EAGER PARSER (FULL AST)' : 'MODE: PREPARSER (LAZY SKIP)';
  const src = state.toks.join(' ') || '// press token keys';
  $('scrSrc').textContent = src.length > 26 ? '…' + src.slice(-25) : src;
  $('scrAst').textContent = 'AST: ' + res.tree;
  const modeKey = keys.get('mode');
  if (modeKey) {
    modeKey.classList.toggle('sel', state.eager);
    modeKey.querySelector('text').textContent = state.eager ? 'EAGER' : 'LAZY';
  }
  $('readout').textContent = (state.eager ? 'eager' : 'lazy') + ' · ' + state.toks.length + ' tok · ' + res.ast + ' ast';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'mode') state.eager = !state.eager;
  else if (k === 'pop') state.toks.pop();
  else if (k === 'clr') state.toks = [];
  else if (state.toks.length < 12) state.toks.push(k);
  render();
}

stage.addEventListener('pointerdown', e => {
  const el = e.target.closest('.press');
  if (el) { e.preventDefault(); act(el.dataset.k); }
});
const KMAP = { '1':'fn', '2':'(x)', '3':'=>', '4':'x', '5':'+', '6':'*', '7':'2', '8':'{ret}', 'm':'mode', 'Backspace':'pop', 'Escape':'clr', '+':'+', '*':'*', 'x':'x' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KMAP[e.key] || KMAP[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
});

// ============================================================================
// 2B: V8 Ignition Bytecode & Inline-Cache Sequencer
// ============================================================================
const page02 = makeIsoPage({
  slug: "iso-02-ignition",
  fig: "Fig 2B",
  title: "Ignition & FeedbackVector Sequencer",
  hint: "press object maps · watch ic transition",
  initialReadout: "mono · 1 map · acc 10 · 4 cyc",
  viewBox: "0 0 610 388",
  ariaLabel: "Isometric V8 Ignition interpreter and FeedbackVector inline cache console. Press Map keys 1-5 to dispatch property loads across shapes, Space to step, or C to clear.",
  footHelp: "Dispatch shapes: <kbd>1</kbd>–<kbd>4</kbd> cache up to 4 Maps in the FeedbackVector (Monomorphic → Polymorphic); <kbd>5</kbd> overflows into <kbd>MEGAMORPHIC</kbd> · <kbd>C</kbd> resets IC.",
  scriptBody: `
const C = Math.cos(Math.PI/6), S = Math.sin(Math.PI/6), OX = 250, OY = 96;
const P = (x,y,z) => [(x-y)*C + OX, (x+y)*S - z + OY];
const D = (x,y,z) => [(x-y)*C, (x+y)*S - z];
const plane = (O,U,V) => { const o=P(...O), u=D(...U), v=D(...V); return \`matrix(\${u[0]} \${u[1]} \${v[0]} \${v[1]} \${o[0]} \${o[1]})\`; };
const TOP = (x,y,z) => plane([x,y,z],[1,0,0],[0,1,0]);
const FRONT = (x,y,z) => plane([x,y,z],[1,0,0],[0,0,-1]);
const SIDE = (x,y,z) => plane([x,y,z],[0,-1,0],[0,0,-1]);
const rect = (t,w,h,r=0,cls='face') => \`<g transform="\${t}"><rect class="\${cls}" width="\${w}" height="\${h}" rx="\${r}"/></g>\`;
const box = (x,y,z,w,d,h,r=0) => rect(SIDE(x+w,y+d,z+h),d,h,Math.min(r,h/4)) + rect(FRONT(x,y+d,z+h),w,h,Math.min(r,h/4)) + rect(TOP(x,y,z+h),w,d,r,'face top');

const W = 344, DECK = 20, RH = 68;
let svg = box(0,0,0, W,216,DECK, 8);
svg += box(0,0,DECK, W,62,RH, 6);
svg += \`<g transform="\${FRONT(0,62,DECK+RH)}">
  <defs><clipPath id="scr2"><rect x="16" y="8" width="248" height="50" rx="5"/></clipPath></defs>
  <rect class="face glass" x="16" y="8" width="248" height="50" rx="5"/>
  <g clip-path="url(#scr2)">
    <text id="icState" class="lcd" x="24" y="22" font-size="10">IC: MONOMORPHIC (4 CYC)</text>
    <text id="bcOp" class="lcd-dim" x="24" y="36" font-size="8.8">LdaNamedProperty a0, [slot 0]</text>
    <text id="accLine" class="lcd" x="24" y="50" font-size="9.5">acc = 10 · hits = 1</text>
  </g>
  \${Array.from({length:6},(_,i)=>\`<path class="detail" d="M\${280+i*8} 12v42"/>\`).join('')}
</g>\`;

// 4 FeedbackVector physical IC slot blocks on upper deck (y = 74)
for (let i = 0; i < 4; i++) {
  const x = 18 + i*54;
  svg += \`<g class="cell" id="slot\${i}">\${box(x,74,DECK, 46,22,6, 3)}<g transform="\${TOP(x,74,DECK+6)}"><text id="slotTxt\${i}" fill="var(--ink-hi)" font-size="8" x="23" y="14" text-anchor="middle">--</text></g></g>\`;
}
// Clear IC button on right of slot row
svg += \`<g class="press op" data-k="clr">\${box(248,74,DECK, 76,22,6, 3)}<g transform="\${TOP(248,74,DECK+6)}"><text x="38" y="14.5" font-size="9">RESET IC</text></g></g>\`;

// 5 Object Shape Map keys (y = 112 and y = 156)
const MAPS = [
  ['M1','Map#1 {x}','1', 10],
  ['M2','Map#2 {x,y}','2', 20],
  ['M3','Map#3 {y,x}','3', 30],
  ['M4','Map#4 {z,x}','4', 40],
  ['M5','Map#5 {w,x}','5', 50],
  ['step','ADD ACC',' ', 0]
];
MAPS.forEach(([id,lbl],idx) => {
  const r = Math.floor(idx / 3), c = idx % 3;
  const x = 18 + c*106, y = 112 + r*44;
  const op = id === 'M5' || id === 'step';
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(x,y,DECK, 96,32,8, 4)}<g transform="\${TOP(x,y,DECK+8)}"><text x="48" y="20" font-size="10">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const VALS = { M1: 10, M2: 20, M3: 30, M4: 40, M5: 50 };
const st = { seen: ['M1'], acc: 10, calls: 1, lastMap: 'M1' };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(el => [el.dataset.k, el]));

function icInfo(n) {
  if (n === 0) return { name: 'UNINITIALIZED', short: 'uninit', cyc: 42 };
  if (n === 1) return { name: 'MONOMORPHIC', short: 'mono', cyc: 4 };
  if (n <= 4) return { name: 'POLYMORPHIC (' + n + ')', short: 'poly-' + n, cyc: 6 + n * 3 };
  return { name: 'MEGAMORPHIC', short: 'mega', cyc: 29 };
}

function render() {
  const info = icInfo(st.seen.length);
  $('icState').textContent = 'IC: ' + info.name + ' (' + info.cyc + ' CYC)';
  $('bcOp').textContent = st.seen.length > 4 ? 'Call LoadIC_MegamorphicStub' : 'LdaNamedProperty a0, [slot 0]';
  $('accLine').textContent = 'acc = ' + st.acc + ' · dispatches = ' + st.calls;
  for (let i = 0; i < 4; i++) {
    const cell = $('slot' + i), txt = $('slotTxt' + i);
    const m = st.seen[i];
    cell.classList.toggle('lit', st.seen.length <= 4 && Boolean(m));
    txt.textContent = st.seen.length > 4 ? 'MEGA' : (m || '--');
    txt.setAttribute('fill', st.seen.length <= 4 && m ? 'var(--ko-ink)' : 'var(--ink)');
  }
  $('readout').textContent = info.short + ' · ' + st.seen.length + (st.seen.length === 1 ? ' map · acc ' : ' maps · acc ') + st.acc + ' · ' + info.cyc + ' cyc';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'clr') { st.seen = []; st.acc = 0; st.calls = 0; }
  else if (k === 'step') { st.acc += VALS[st.lastMap] || 1; st.calls++; }
  else if (k in VALS) {
    if (!st.seen.includes(k)) st.seen.push(k);
    st.lastMap = k;
    st.acc = VALS[k];
    st.calls++;
  }
  render();
}

stage.addEventListener('pointerdown', e => {
  const el = e.target.closest('.press');
  if (el) { e.preventDefault(); act(el.dataset.k); }
});
const KMAP = { '1':'M1', '2':'M2', '3':'M3', '4':'M4', '5':'M5', ' ':'step', 'Enter':'step', 'c':'clr', 'Escape':'clr' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KMAP[e.key] || KMAP[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
});

// ============================================================================
// 3B: V8 Maglev / TurboFan Speculative JIT & Deopt Console
// ============================================================================
const page03 = makeIsoPage({
  slug: "iso-03-turbofan",
  fig: "Fig 3B",
  title: "TurboFan Tier-Up & Deopt Console",
  hint: "warm smi loop · inject float or wrong map",
  initialReadout: "turbofan · guarded · 1.0 ns",
  viewBox: "0 0 610 388",
  ariaLabel: "Isometric V8 Maglev and TurboFan JIT console. Press S to warm hot Smi calls, F to pass a HeapNumber float, M for a wrong Map, G to toggle CheckMaps guard, or Escape to reset.",
  footHelp: "Keys: <kbd>S</kbd> hot Smi call (tiers Ignition → Sparkplug → Maglev → TurboFan) · <kbd>F</kbd> HeapNumber · <kbd>M</kbd> WrongMap · <kbd>G</kbd> toggle CheckMaps guard · <kbd>Esc</kbd> reset.",
  scriptBody: `
const C = Math.cos(Math.PI/6), S = Math.sin(Math.PI/6), OX = 250, OY = 96;
const P = (x,y,z) => [(x-y)*C + OX, (x+y)*S - z + OY];
const D = (x,y,z) => [(x-y)*C, (x+y)*S - z];
const plane = (O,U,V) => { const o=P(...O), u=D(...U), v=D(...V); return \`matrix(\${u[0]} \${u[1]} \${v[0]} \${v[1]} \${o[0]} \${o[1]})\`; };
const TOP = (x,y,z) => plane([x,y,z],[1,0,0],[0,1,0]);
const FRONT = (x,y,z) => plane([x,y,z],[1,0,0],[0,0,-1]);
const SIDE = (x,y,z) => plane([x,y,z],[0,-1,0],[0,0,-1]);
const rect = (t,w,h,r=0,cls='face') => \`<g transform="\${t}"><rect class="\${cls}" width="\${w}" height="\${h}" rx="\${r}"/></g>\`;
const box = (x,y,z,w,d,h,r=0) => rect(SIDE(x+w,y+d,z+h),d,h,Math.min(r,h/4)) + rect(FRONT(x,y+d,z+h),w,h,Math.min(r,h/4)) + rect(TOP(x,y,z+h),w,d,r,'face top');

const W = 344, DECK = 20, RH = 68;
let svg = box(0,0,0, W,216,DECK, 8);
svg += box(0,0,DECK, W,62,RH, 6);
svg += \`<g transform="\${FRONT(0,62,DECK+RH)}">
  <defs><clipPath id="scr3"><rect x="16" y="8" width="248" height="50" rx="5"/></clipPath></defs>
  <rect class="face glass" x="16" y="8" width="248" height="50" rx="5"/>
  <g clip-path="url(#scr3)">
    <text id="jitTier" class="lcd" x="24" y="22" font-size="10">TIER: TURBOFAN (OPT MACHINE)</text>
    <text id="jitGuard" class="lcd-dim" x="24" y="36" font-size="8.8">GUARD: CheckSmi + CheckMaps#1</text>
    <text id="jitEvent" class="lcd" x="24" y="50" font-size="9.2">Int32Add(42, 1) -&gt; 43 [1.0 ns]</text>
  </g>
  \${Array.from({length:6},(_,i)=>\`<path class="detail" d="M\${280+i*8} 12v42"/>\`).join('')}
</g>\`;

// 4 Tier indicator blocks on upper deck (Ignition, Sparkplug, Maglev, TurboFan)
const TIERS = ['IGN','SPK','MAG','TFN'];
TIERS.forEach((t,i) => {
  const x = 18 + i*54;
  svg += \`<g class="cell" id="tier\${i}">\${box(x,74,DECK, 46,22,6, 3)}<g transform="\${TOP(x,74,DECK+6)}"><text id="tierTxt\${i}" fill="var(--ink)" font-size="8" x="23" y="14" text-anchor="middle">\${t}</text></g></g>\`;
});
svg += \`<g class="press" data-k="guard">\${box(244,74,DECK, 82,22,6, 3)}<g transform="\${TOP(244,74,DECK+6)}"><text id="guardBtnTxt" x="41" y="14.5" font-size="8.5">GUARD: ON</text></g></g>\`;

const KEYS = [
  ['smi','CALL(Smi 42)', true],
  ['flt','CALL(1.5)', false],
  ['map','CALL(Map#9)', false],
  ['warm','WARM +4', false],
  ['deopt','BAILOUT', false],
  ['rst','RESET', false]
];
KEYS.forEach(([id,lbl,op],idx) => {
  const r = Math.floor(idx / 3), c = idx % 3;
  const x = 18 + c*106, y = 112 + r*44;
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(x,y,DECK, 96,32,8, 4)}<g transform="\${TOP(x,y,DECK+8)}"><text x="48" y="20" font-size="9.5">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const TIER_NAMES = ['IGNITION', 'SPARKPLUG', 'MAGLEV', 'TURBOFAN'];
const TIER_NS = ['18.0 ns', '9.5 ns', '2.4 ns', '1.0 ns'];
const st = { tier: 3, hot: 8, guarded: true, deopts: 0, msg: 'Int32Add(42, 1) -> 43', hazard: false };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(el => [el.dataset.k, el]));

function syncTierFromHot() {
  if (st.hot >= 7) st.tier = 3;
  else if (st.hot >= 4) st.tier = 2;
  else if (st.hot >= 2) st.tier = 1;
  else st.tier = 0;
}

function render() {
  $('jitTier').textContent = st.hazard ? 'HAZARD: TYPE CONFUSION (OOB!)' : 'TIER: ' + TIER_NAMES[st.tier] + ' (HOT=' + st.hot + ')';
  $('jitGuard').textContent = st.guarded ? 'GUARD: CheckSmi + CheckMaps#1' : 'GUARD: ELIDED (UNSAFE JIT ASSUMPTION!)';
  $('jitEvent').textContent = st.msg;
  $('guardBtnTxt').textContent = st.guarded ? 'GUARD: ON' : 'GUARD: OFF';
  keys.get('guard').classList.toggle('sel', st.guarded);
  for (let i = 0; i < 4; i++) {
    const c = $('tier' + i), t = $('tierTxt' + i);
    const active = i === st.tier && !st.hazard;
    c.classList.toggle('lit', active);
    t.setAttribute('fill', active ? 'var(--ko-ink)' : 'var(--ink)');
  }
  const ns = st.hazard ? 'cve oob!' : TIER_NS[st.tier];
  $('readout').textContent = (st.hazard ? 'type confusion' : TIER_NAMES[st.tier].toLowerCase()) + ' · ' + (st.guarded ? 'guarded' : 'unguarded') + ' · ' + ns;
}

function mismatch(reason) {
  if (st.tier >= 2) {
    if (st.guarded) {
      st.tier = 0; st.hot = 0; st.deopts++; st.hazard = false;
      st.msg = 'DEOPT (' + reason + ') -> Ignition #' + st.deopts;
    } else {
      st.hazard = true;
      st.msg = 'UNCHECKED ' + reason + ' -> OOB FIELD READ!';
    }
  } else {
    st.hazard = false;
    st.msg = 'Generic IC handled ' + reason + ' safely';
  }
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'smi') { st.hazard = false; st.hot++; syncTierFromHot(); st.msg = st.tier >= 2 ? 'Int32Add(42, 1) -> 43 [fast]' : 'Bytecode AddSmi -> 43'; }
  else if (k === 'warm') { st.hazard = false; st.hot += 4; syncTierFromHot(); st.msg = 'OSR tier-up -> ' + TIER_NAMES[st.tier]; }
  else if (k === 'flt') mismatch('NotASmi 1.5');
  else if (k === 'map' || k === 'deopt') mismatch('WrongMap#9');
  else if (k === 'guard') { st.guarded = !st.guarded; st.hazard = false; st.msg = st.guarded ? 'Restored CheckMaps guard' : 'Warning: guard elided in JIT'; }
  else if (k === 'rst') { Object.assign(st, { tier: 0, hot: 0, guarded: true, deopts: 0, hazard: false, msg: 'Reset to Ignition cold entry' }); }
  render();
}

stage.addEventListener('pointerdown', e => {
  const el = e.target.closest('.press');
  if (el) { e.preventDefault(); act(el.dataset.k); }
});
const KMAP = { 's':'smi', 'f':'flt', 'm':'map', 'w':'warm', 'd':'deopt', 'g':'guard', 'Escape':'rst', ' ':'smi' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KMAP[e.key] || KMAP[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
});

// ============================================================================
// 4B: V8 HiddenClass (Map) & Orinoco Tricolor Heap Workbench
// ============================================================================
const page04 = makeIsoPage({
  slug: "iso-04-orinoco",
  fig: "Fig 4B",
  title: "HiddenClass & Orinoco GC Workbench",
  hint: "alloc objects · transition maps · sweep",
  initialReadout: "map2 {x,y} · 3 live / 1 dead · 32 B",
  viewBox: "0 0 610 392",
  ariaLabel: "Isometric V8 HiddenClass and Orinoco garbage collector console. Press A to allocate, X and Y to add fields, U to drop root, M to mark, and C to sweep and compact.",
  footHelp: "Keys: <kbd>A</kbd> allocate Nursery cell · <kbd>X</kbd> / <kbd>Y</kbd> transition HiddenClass (<kbd>M0→M1→M2</kbd>) · <kbd>U</kbd> unroot cell · <kbd>M</kbd> tricolor mark · <kbd>C</kbd> compact To-Space.",
  scriptBody: `
const C = Math.cos(Math.PI/6), S = Math.sin(Math.PI/6), OX = 250, OY = 96;
const P = (x,y,z) => [(x-y)*C + OX, (x+y)*S - z + OY];
const D = (x,y,z) => [(x-y)*C, (x+y)*S - z];
const plane = (O,U,V) => { const o=P(...O), u=D(...U), v=D(...V); return \`matrix(\${u[0]} \${u[1]} \${v[0]} \${v[1]} \${o[0]} \${o[1]})\`; };
const TOP = (x,y,z) => plane([x,y,z],[1,0,0],[0,1,0]);
const FRONT = (x,y,z) => plane([x,y,z],[1,0,0],[0,0,-1]);
const SIDE = (x,y,z) => plane([x,y,z],[0,-1,0],[0,0,-1]);
const rect = (t,w,h,r=0,cls='face') => \`<g transform="\${t}"><rect class="\${cls}" width="\${w}" height="\${h}" rx="\${r}"/></g>\`;
const box = (x,y,z,w,d,h,r=0) => rect(SIDE(x+w,y+d,z+h),d,h,Math.min(r,h/4)) + rect(FRONT(x,y+d,z+h),w,h,Math.min(r,h/4)) + rect(TOP(x,y,z+h),w,d,r,'face top');

const W = 344, DECK = 20, RH = 68;
let svg = box(0,0,0, W,218,DECK, 8);
svg += box(0,0,DECK, W,62,RH, 6);
svg += \`<g transform="\${FRONT(0,62,DECK+RH)}">
  <defs><clipPath id="scr4"><rect x="16" y="8" width="248" height="50" rx="5"/></clipPath></defs>
  <rect class="face glass" x="16" y="8" width="248" height="50" rx="5"/>
  <g clip-path="url(#scr4)">
    <text id="mapChain" class="lcd" x="24" y="22" font-size="9.5">MAP: M0{} -&gt; M1{+x@4} -&gt; M2{+y@8}</text>
    <text id="gcPhase" class="lcd-dim" x="24" y="36" font-size="8.8">ORINOCO: NURSERY + TRICOLOR MARK</text>
    <text id="heapStat" class="lcd" x="24" y="50" font-size="9.2">3 rooted · 1 unreachable · 32 B</text>
  </g>
  \${Array.from({length:6},(_,i)=>\`<path class="detail" d="M\${280+i*8} 12v42"/>\`).join('')}
</g>\`;

// 6 Isometric Heap Cell Blocks on upper deck (y = 74)
for (let i = 0; i < 6; i++) {
  const x = 18 + i*52;
  svg += \`<g class="cell" id="hcell\${i}">\${box(x,74,DECK, 44,24,7, 3)}<g transform="\${TOP(x,74,DECK+7)}"><text id="htxt\${i}" fill="var(--ink)" font-size="7.5" x="22" y="15" text-anchor="middle">FREE</text></g></g>\`;
}

// 6 Control Keys (2 rows x 3 cols)
const KEYS = [
  ['alloc','ALLOC OBJ', true],
  ['addx','ADD .x (+4)', false],
  ['addy','ADD .y (+8)', false],
  ['unroot','DROP ROOT', false],
  ['mark','MARK LIVE', false],
  ['sweep','COMPACT', true]
];
KEYS.forEach(([id,lbl,op],idx) => {
  const r = Math.floor(idx / 3), c = idx % 3;
  const x = 18 + c*106, y = 114 + r*44;
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(x,y,DECK, 96,32,8, 4)}<g transform="\${TOP(x,y,DECK+8)}"><text x="48" y="20" font-size="9.5">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = {
  cells: [
    { map: 2, root: true, mark: 'B' },
    { map: 1, root: true, mark: 'B' },
    { map: 0, root: false, mark: 'W' },
    { map: 2, root: true, mark: 'B' },
    null,
    null
  ],
  freedTotal: 0,
  status: 'ORINOCO: READY (4 SLOTS USED)'
};
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(el => [el.dataset.k, el]));

function render() {
  let maxMap = 0, live = 0, dead = 0, bytes = 0;
  for (let i = 0; i < 6; i++) {
    const c = st.cells[i], el = $('hcell' + i), t = $('htxt' + i);
    if (!c) {
      el.classList.remove('lit', 'mid');
      t.textContent = 'FREE';
      t.setAttribute('fill', 'var(--ink)');
    } else {
      maxMap = Math.max(maxMap, c.map);
      if (c.root) live++; else dead++;
      bytes += 4 + c.map * 4;
      const isLit = c.root && c.mark === 'B';
      el.classList.toggle('lit', isLit);
      el.classList.toggle('mid', !isLit);
      t.textContent = 'M' + c.map + (c.root ? '·R' : '·W');
      t.setAttribute('fill', isLit ? 'var(--ko-ink)' : 'var(--ink-hi)');
    }
  }
  const chain = maxMap === 0 ? 'M0{} (4B header)' : maxMap === 1 ? 'M0{} -> M1{+x@4}' : 'M0{} -> M1{+x@4} -> M2{+y@8}';
  $('mapChain').textContent = 'MAP: ' + chain;
  $('gcPhase').textContent = st.status;
  $('heapStat').textContent = live + ' live · ' + dead + ' dead · ' + bytes + ' B (' + st.freedTotal + ' B swept)';
  $('readout').textContent = 'map' + maxMap + ' · ' + live + ' live / ' + dead + ' dead · ' + bytes + ' B';
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'alloc') {
    const freeIdx = st.cells.findIndex(c => c === null);
    if (freeIdx >= 0) { st.cells[freeIdx] = { map: 0, root: true, mark: 'W' }; st.status = 'NURSERY: BUMP ALLOCATED SLOT ' + freeIdx; }
    else st.status = 'NURSERY FULL -> RUN COMPACT!';
  } else if (k === 'addx' || k === 'addy') {
    const target = [...st.cells].reverse().find(c => c && c.root);
    if (target) {
      target.map = k === 'addx' ? Math.max(target.map, 1) : 2;
      st.status = 'TRANSITIONED -> Map#' + target.map + ' (in-object +' + (target.map * 4) + ')';
    }
  } else if (k === 'unroot') {
    const idx = st.cells.findIndex(c => c && c.root);
    if (idx >= 0) { st.cells[idx].root = false; st.cells[idx].mark = 'W'; st.status = 'DROPPED HANDLE ON SLOT ' + idx + ' (WHITE)'; }
  } else if (k === 'mark') {
    st.cells.forEach(c => { if (c) c.mark = c.root ? 'B' : 'W'; });
    st.status = 'TRICOLOR MARK: ROOTED -> BLACK';
  } else if (k === 'sweep') {
    let swept = 0;
    const survivors = [];
    st.cells.forEach(c => {
      if (c && c.root) { c.mark = 'B'; survivors.push(c); }
      else if (c) { swept += 4 + c.map * 4; }
    });
    while (survivors.length < 6) survivors.push(null);
    st.cells = survivors;
    st.freedTotal += swept;
    st.status = 'SCAVENGER COMPACTED -> FREED ' + swept + ' B';
  }
  render();
}

stage.addEventListener('pointerdown', e => {
  const el = e.target.closest('.press');
  if (el) { e.preventDefault(); act(el.dataset.k); }
});
const KMAP = { 'a':'alloc', 'x':'addx', 'y':'addy', 'u':'unroot', 'm':'mark', 'c':'sweep', ' ':'sweep' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KMAP[e.key] || KMAP[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
});

// ============================================================================
// 5B: V8 Liftoff WebAssembly Decoder & Linear-Memory Sandbox Unit
// ============================================================================
const page05 = makeIsoPage({
  slug: "iso-05-liftoff",
  fig: "Fig 5B",
  title: "Liftoff Wasm & Guard-Zone Unit",
  hint: "run stack ops · probe linear memory",
  initialReadout: "liftoff · 1 page (64k) · tos 32",
  viewBox: "0 0 610 392",
  ariaLabel: "Isometric V8 Liftoff WebAssembly baseline compiler and linear memory sandbox console. Press 1 to push i32, A to add, S to store, L to load in-bounds, O to test out-of-bounds guard trap, G to grow memory, T to tier up, Escape to reset.",
  footHelp: "Keys: <kbd>1</kbd> i32.const 16 · <kbd>A</kbd> i32.add · <kbd>S</kbd> i32.store [0] · <kbd>L</kbd> i32.load [0] · <kbd>O</kbd> i32.load [OOB] (guard trap!) · <kbd>G</kbd> memory.grow · <kbd>T</kbd> tier · <kbd>Esc</kbd> reset.",
  scriptBody: `
const C = Math.cos(Math.PI/6), S = Math.sin(Math.PI/6), OX = 250, OY = 96;
const P = (x,y,z) => [(x-y)*C + OX, (x+y)*S - z + OY];
const D = (x,y,z) => [(x-y)*C, (x+y)*S - z];
const plane = (O,U,V) => { const o=P(...O), u=D(...U), v=D(...V); return \`matrix(\${u[0]} \${u[1]} \${v[0]} \${v[1]} \${o[0]} \${o[1]})\`; };
const TOP = (x,y,z) => plane([x,y,z],[1,0,0],[0,1,0]);
const FRONT = (x,y,z) => plane([x,y,z],[1,0,0],[0,0,-1]);
const SIDE = (x,y,z) => plane([x,y,z],[0,-1,0],[0,0,-1]);
const rect = (t,w,h,r=0,cls='face') => \`<g transform="\${t}"><rect class="\${cls}" width="\${w}" height="\${h}" rx="\${r}"/></g>\`;
const box = (x,y,z,w,d,h,r=0) => rect(SIDE(x+w,y+d,z+h),d,h,Math.min(r,h/4)) + rect(FRONT(x,y+d,z+h),w,h,Math.min(r,h/4)) + rect(TOP(x,y,z+h),w,d,r,'face top');

const W = 344, DECK = 20, RH = 68;
let svg = box(0,0,0, W,218,DECK, 8);
svg += box(0,0,DECK, W,62,RH, 6);
svg += \`<g transform="\${FRONT(0,62,DECK+RH)}">
  <defs><clipPath id="scr5"><rect x="16" y="8" width="248" height="50" rx="5"/></clipPath></defs>
  <rect class="face glass" x="16" y="8" width="248" height="50" rx="5"/>
  <g clip-path="url(#scr5)">
    <text id="wTier" class="lcd" x="24" y="22" font-size="9.5">TIER: LIFTOFF 1-PASS · 1x64KiB</text>
    <text id="wOp" class="lcd-dim" x="24" y="36" font-size="8.8">OP: 6a i32.add -&gt; mem[0]=32</text>
    <text id="wStack" class="lcd" x="24" y="50" font-size="9.2">STACK: [ 32 ] · SANDBOX OK</text>
  </g>
  \${Array.from({length:6},(_,i)=>\`<path class="detail" d="M\${280+i*8} 12v42"/>\`).join('')}
</g>\`;

// 4 Linear-memory 64 KiB page blocks + 1 Guard-Zone block on upper deck (y = 74)
for (let i = 0; i < 4; i++) {
  const x = 18 + i*54;
  svg += \`<g class="cell" id="wpage\${i}">\${box(x,74,DECK, 46,22,6, 3)}<g transform="\${TOP(x,74,DECK+6)}"><text id="wpTxt\${i}" fill="var(--ink)" font-size="7.5" x="23" y="14" text-anchor="middle">P\${i}</text></g></g>\`;
}
svg += \`<g class="press" data-k="tier">\${box(244,74,DECK, 82,22,6, 3)}<g transform="\${TOP(244,74,DECK+6)}"><text id="tierBtn" x="41" y="14.5" font-size="8.2">LIFTOFF</text></g></g>\`;

const KEYS = [
  ['const','i32.const 16', false],
  ['add','i32.add', true],
  ['store','store [0]', false],
  ['load','load [0]', false],
  ['oob','load [OOB]', true],
  ['grow','grow +64K', false]
];
KEYS.forEach(([id,lbl,op],idx) => {
  const r = Math.floor(idx / 3), c = idx % 3;
  const x = 18 + c*106, y = 114 + r*44;
  svg += \`<g class="press\${op?' op':''}" data-k="\${id}">\${box(x,y,DECK, 96,32,8, 4)}<g transform="\${TOP(x,y,DECK+8)}"><text x="48" y="20" font-size="9.5">\${lbl}</text></g></g>\`;
});

const stage = document.getElementById('stage');
stage.innerHTML = svg;

const st = { liftoff: true, pages: 1, stack: [32], mem0: 32, trapped: false, op: '6a i32.add -> 32' };
const $ = id => document.getElementById(id);
const keys = new Map([...stage.querySelectorAll('.press')].map(el => [el.dataset.k, el]));

function render() {
  const tierStr = st.liftoff ? 'LIFTOFF 1-PASS' : 'TURBOFAN WASM';
  $('wTier').textContent = 'TIER: ' + tierStr + ' · ' + st.pages + 'x64KiB';
  $('wOp').textContent = 'OP: ' + st.op;
  $('wStack').textContent = st.trapped
    ? 'TRAP: OutOfBounds (0 host B touched)'
    : 'STACK: [ ' + (st.stack.length ? st.stack.slice(-4).join(', ') : 'empty') + ' ] · mem[0]=' + st.mem0;
  $('tierBtn').textContent = st.liftoff ? 'LIFTOFF' : 'TF-WASM';
  keys.get('tier').classList.toggle('sel', !st.liftoff);
  for (let i = 0; i < 4; i++) {
    const active = i < st.pages;
    $('wpage' + i).classList.toggle('lit', active && !st.trapped);
    $('wpTxt' + i).textContent = active ? (i * 64 + 'K') : 'GUARD';
    $('wpTxt' + i).setAttribute('fill', active && !st.trapped ? 'var(--ko-ink)' : 'var(--ink)');
  }
  const tos = st.stack.length ? st.stack[st.stack.length - 1] : 0;
  $('readout').textContent = st.trapped
    ? 'trap: oob contained · ' + (st.pages * 64) + 'k'
    : (st.liftoff ? 'liftoff' : 'tf-wasm') + ' · ' + st.pages + (st.pages === 1 ? ' page · tos ' : ' pages · tos ') + tos;
}

function act(k) {
  const el = keys.get(k);
  if (el) { el.classList.add('down'); setTimeout(() => el.classList.remove('down'), 110); }
  if (k === 'rst') { Object.assign(st, { pages: 1, stack: [16], mem0: 32, trapped: false, op: '41 10 i32.const 16' }); render(); return; }
  if (k === 'tier') { st.liftoff = !st.liftoff; st.trapped = false; st.op = st.liftoff ? 'Baseline Liftoff codegen' : 'Tiered up -> TurboFan Wasm'; render(); return; }
  if (k === 'oob') {
    st.trapped = true;
    st.op = '28 02 FF FF 04 i32.load [0x' + (st.pages * 0x10000).toString(16) + ']';
    render(); return;
  }
  st.trapped = false;
  if (k === 'const') { st.stack.push(16); st.op = '41 10 i32.const 16'; }
  else if (k === 'add') {
    const b = st.stack.pop() ?? 0, a = st.stack.pop() ?? 0;
    st.stack.push((a + b) | 0);
    st.op = '6a i32.add -> ' + ((a + b) | 0);
  } else if (k === 'store') {
    const v = st.stack.pop() ?? 0;
    st.mem0 = v;
    st.op = '36 02 00 i32.store [0] = ' + v;
  } else if (k === 'load') {
    st.stack.push(st.mem0);
    st.op = '28 02 00 i32.load [0] -> ' + st.mem0;
  } else if (k === 'grow') {
    if (st.pages < 4) { st.pages++; st.op = '40 00 memory.grow -> ' + (st.pages * 64) + ' KiB'; }
    else st.op = '40 00 memory.grow -> max 256 KiB demo cap';
  }
  render();
}

stage.addEventListener('pointerdown', e => {
  const el = e.target.closest('.press');
  if (el) { e.preventDefault(); act(el.dataset.k); }
});
const KMAP = { '1':'const', 'a':'add', 's':'store', 'l':'load', 'o':'oob', 'g':'grow', 't':'tier', 'Escape':'rst' };
window.addEventListener('keydown', e => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = KMAP[e.key] || KMAP[e.key.toLowerCase()];
  if (k) { e.preventDefault(); act(k); }
});
render();
`,
});

const ALL = [
  ["iso-01-parser.html", page01],
  ["iso-02-ignition.html", page02],
  ["iso-03-turbofan.html", page03],
  ["iso-04-orinoco.html", page04],
  ["iso-05-liftoff.html", page05],
];

for (const [name, html] of ALL) {
  writeFileSync(join(PAGES_DIR, name), html);
  console.log(`wrote ${name}`);
}
