import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

export const PAGES_DIR = join(dirname(fileURLToPath(import.meta.url)), "pages");
mkdirSync(PAGES_DIR, { recursive: true });

const C = Math.cos(Math.PI / 6);
const S = Math.sin(Math.PI / 6);

/**
 * Step 5 of MrBongoC/ai-iso-skill (skills/iso-figure/SKILL.md):
 * Project the scene's extreme 3D corners [x, y, z, w, d, h] numerically
 * and compute integer OX, OY, and viewBox with ~10% margin on every side.
 */
export function computeFrame(boxes, marginRatio = 0.10) {
  let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
  for (const [x, y, z, w, d, h] of boxes) {
    for (const px of [x, x + w]) {
      for (const py of [y, y + d]) {
        for (const pz of [z, z + h]) {
          const sx = (px - py) * C;
          const sy = (px + py) * S - pz;
          if (sx < minX) minX = sx;
          if (sx > maxX) maxX = sx;
          if (sy < minY) minY = sy;
          if (sy > maxY) maxY = sy;
        }
      }
    }
  }
  const spanX = maxX - minX;
  const spanY = maxY - minY;
  const padX = Math.max(24, spanX * marginRatio);
  const padY = Math.max(22, spanY * marginRatio);
  const vw = Math.ceil(spanX + padX * 2);
  const vh = Math.ceil(spanY + padY * 2);
  const ox = Math.round(padX - minX);
  const oy = Math.round(padY - minY);
  return { ox, oy, vw, vh };
}

export function writeIsoFigure({
  slug,
  fig,
  title,
  hint,
  initialReadout,
  ariaLabel,
  footHelp,
  bounds,
  extraCss = "",
  sceneJs,
}) {
  const { ox, oy, vw, vh } = computeFrame(bounds);
  const html = `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${fig} — ${title}</title>
<style>
  :root {
    color-scheme: dark;
    --bg:#0c0d0e; --panel:#141516; --edge:#222426;
    --line:#3e4347; --detail:#2a2d30; --body:#17181a; --deck:#1c1e21;
    --ink:#868b8f; --ink-hi:#e6e8e9; --live:#f4f5f5;
    --kn:#232629; --kn-line:#565b5f; --ko:#d9dcde; --ko-line:#5a5f63; --ko-ink:#141618;
    --glass:#0a0b0c;
    --mono:"JetBrains Mono","SF Mono",ui-monospace,Menlo,Consolas,monospace;
  }
  @media (prefers-color-scheme: light) { :root:not([data-theme="dark"]) {
    color-scheme: light;
    --bg:#e9eaea; --panel:#f6f6f5; --edge:#d6d8d8;
    --line:#8b9095; --detail:#c3c6c8; --body:#ececeb; --deck:#f3f3f2;
    --ink:#5f6468; --ink-hi:#16181a; --live:#0c0d0e;
    --kn:#ffffff; --kn-line:#7b8084; --ko:#242628; --ko-line:#0c0d0e; --ko-ink:#f4f5f5;
    --glass:#e1e3e3;
  } }
  :root[data-theme="light"] {
    color-scheme: light;
    --bg:#e9eaea; --panel:#f6f6f5; --edge:#d6d8d8;
    --line:#8b9095; --detail:#c3c6c8; --body:#ececeb; --deck:#f3f3f2;
    --ink:#5f6468; --ink-hi:#16181a; --live:#0c0d0e;
    --kn:#ffffff; --kn-line:#7b8084; --ko:#242628; --ko-line:#0c0d0e; --ko-ink:#f4f5f5;
    --glass:#e1e3e3;
  }
  * { box-sizing:border-box; }
  body { margin:0; background:var(--bg); color:var(--ink); font-family:var(--mono); font-size:13px; padding:20px 16px; }
  html[data-embed="1"] body { background:transparent; padding:0; }
  html[data-embed="1"] main { max-width:none; }
  html[data-embed="1"] .foot-help { display:none; }
  html[data-embed="1"] svg { aspect-ratio: 6 / 5; }
  html[data-compact="1"] figure { padding:12px 14px; border-radius:12px; }
  html[data-compact="1"] .cap { font-size:10.5px; letter-spacing:.09em; }
  main { max-width:820px; margin-inline:auto; display:grid; gap:12px; }
  figure { margin:0; background:var(--panel); border:1px solid var(--edge); border-radius:20px; padding:20px 24px; display:grid; gap:6px; }
  .cap { display:flex; flex-wrap:wrap; justify-content:space-between; align-items:baseline; gap:4px 16px; font-size:12px; text-transform:uppercase; letter-spacing:.13em; }
  .cap .hi { color:var(--ink-hi); text-transform:none; letter-spacing:.04em; }
  svg { width:100%; height:auto; display:block; touch-action:manipulation; user-select:none; -webkit-user-select:none; }
  svg:focus-visible { outline:2px solid var(--live); outline-offset:4px; border-radius:8px; }
  .face { fill:var(--body); stroke:var(--line); stroke-width:1; vector-effect:non-scaling-stroke; stroke-linejoin:round; }
  .face.top { fill:var(--deck); }
  .detail { fill:none; stroke:var(--detail); stroke-width:1; vector-effect:non-scaling-stroke; stroke-linejoin:round; }
  .struct { fill:none; stroke:var(--line); stroke-width:1; vector-effect:non-scaling-stroke; stroke-linejoin:round; }
  .live-stroke { fill:none; stroke:var(--live); stroke-width:1.25; vector-effect:non-scaling-stroke; stroke-linejoin:round; }
  .glass { fill:var(--glass); }
  .lcd { fill:var(--live); font-family:var(--mono); }
  .lcd-dim { fill:var(--ink); font-family:var(--mono); }
  .lbl { fill:var(--ink); font-family:var(--mono); text-anchor:middle; pointer-events:none; }
  .lbl-hi { fill:var(--ink-hi); font-family:var(--mono); text-anchor:middle; pointer-events:none; }
  .press { cursor:pointer; transition:transform 60ms ease-out; }
  .press .face { fill:var(--kn); stroke:var(--kn-line); transition:stroke 90ms, fill 90ms; }
  .press.op .face { fill:var(--ko); stroke:var(--ko-line); }
  .press text { fill:var(--ink-hi); font-family:var(--mono); text-anchor:middle; pointer-events:none; }
  .press.op text { fill:var(--ko-ink); }
  .press.down { transform:translateY(4px); }
  .press.down .face, .press:hover .face.top, .press.sel .face { stroke:var(--live); }
  .press.sel text { fill:var(--live); }
  .press.op.sel text { fill:var(--ko-ink); }
  .unit { transition:transform 160ms cubic-bezier(.22,.8,.24,1); }
  .unit .face { transition:stroke 120ms, fill 120ms; }
  .unit.lit .face { stroke:var(--live); }
  .unit.lit .face.top { fill:var(--ko); }
  .unit.lit .lbl-hi { fill:var(--live); }
  .unit.lit .top-lbl { fill:var(--ko-ink); }
  .top-lbl { fill:var(--ink-hi); font-family:var(--mono); text-anchor:middle; pointer-events:none; }
  .unit.mid .face { stroke:var(--kn-line); }
  .foot-help { margin:0; max-width:68ch; line-height:1.6; font-size:12px; }
  kbd { font:inherit; color:var(--ink-hi); border:1px solid var(--edge); border-radius:4px; padding:0 4px; }
  @media (prefers-reduced-motion:reduce){ .press, .unit { transition:none !important; } }
  ${extraCss}
</style>
</head>
<body>
<main>
  <figure class="iso-plate">
    <div class="cap"><span class="hi">${fig}</span><span>${title}</span></div>
    <svg id="stage" viewBox="0 0 ${vw} ${vh}" tabindex="0" role="img" aria-label="${ariaLabel}"></svg>
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

// ---- iso kernel (verbatim MrBongoC/ai-iso-skill) ----
const C = Math.cos(Math.PI/6), S = Math.sin(Math.PI/6), OX = ${ox}, OY = ${oy};
const P = (x,y,z) => [(x-y)*C + OX, (x+y)*S - z + OY];
const D = (x,y,z) => [(x-y)*C, (x+y)*S - z];
const plane = (O,U,V) => { const o=P(...O), u=D(...U), v=D(...V); return \`matrix(\${u[0]} \${u[1]} \${v[0]} \${v[1]} \${o[0]} \${o[1]})\`; };
const TOP = (x,y,z) => plane([x,y,z],[1,0,0],[0,1,0]);
const FRONT = (x,y,z) => plane([x,y,z],[1,0,0],[0,0,-1]);
const SIDE = (x,y,z) => plane([x,y,z],[0,-1,0],[0,0,-1]);
const rect = (t,w,h,r=0,cls='face') => \`<g transform="\${t}"><rect class="\${cls}" width="\${w}" height="\${h}" rx="\${r}"/></g>\`;
const box = (x,y,z,w,d,h,r=0) => rect(SIDE(x+w,y+d,z+h),d,h,Math.min(r,h/4)) + rect(FRONT(x,y+d,z+h),w,h,Math.min(r,h/4)) + rect(TOP(x,y,z+h),w,d,r,'face top');

${sceneJs}
</script>
</body>
</html>`;
  const outPath = join(PAGES_DIR, `${slug}.html`);
  writeFileSync(outPath, html);
  console.log(`wrote ${slug}.html (${vw}x${vh})`);
}
