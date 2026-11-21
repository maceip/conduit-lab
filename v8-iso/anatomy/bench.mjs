import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import { tubePieces, tubeSvg } from "../kit/tube.mjs";
import * as A from "../kit/audit.mjs";
import { kitScript } from "../scripts/inline-kit.mjs";

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..");
export const PAGES_DIR = join(ROOT, "pages");

export const EMBED_HOOK_CSS = `
html[data-embed="1"] body { background: transparent; }
html[data-embed="1"] .iso-page { width: 100%; max-width: none; margin: 0; }
html[data-embed="1"] .iso-figure { margin: 0; }
html[data-compact="1"] .iso-legend { display: none; }
html[data-compact="1"] .iso-plate { border-radius: 10px; }
.iso-stage:focus-visible { outline: 1px solid var(--anatomy-muted); outline-offset: 6px; border-radius: 8px; }
`;

export const EMBED_HOOK_JS = `
(() => {
  const params = new URLSearchParams(location.search);
  if (params.get("embed") === "1") {
    document.documentElement.setAttribute("data-embed", "1");
  }
  if (params.get("compact") === "1") {
    document.documentElement.setAttribute("data-compact", "1");
  }
  const qTheme = params.get("theme");
  if (qTheme === "light" || qTheme === "dark") {
    document.body.setAttribute("data-theme", qTheme);
    document.documentElement.style.colorScheme = qTheme;
  }
  window.addEventListener("message", (ev) => {
    if (ev.data && ev.data.type === "v8-iso-theme" && (ev.data.theme === "light" || ev.data.theme === "dark")) {
      document.body.setAttribute("data-theme", ev.data.theme);
      document.documentElement.style.colorScheme = ev.data.theme;
    }
  });
  if (params.get("embed") === "1" && window.parent && window.parent !== window) {
    const postHeight = () => {
      const el = document.querySelector(".iso-page") || document.body;
      const h = Math.ceil(el.getBoundingClientRect().height);
      if (h > 0) window.parent.postMessage({ type: "v8-iso-height", id: params.get("id") || "", height: h }, "*");
    };
    new ResizeObserver(postHeight).observe(document.body);
    window.addEventListener("load", postHeight);
    setTimeout(postHeight, 60);
  }
})();
`;

export function createBench(P, { order = [], spring = {} } = {}) {
  const R = A.recorder(P, { order, spring });
  const KS = G.scaleOf(P);
  const at = (pt) => k.iso(pt, P);
  const S = (paths, style) => k.solidSvg(paths, style);
  const Ln = (d, style) => k.lineSvg(d, style);
  const Dots = (pts, style) => k.dotsSvg(pts, style);
  const byDepth = (pts) =>
    [...pts].sort((a, b) => k.depthOf([a[0], a[1], 0], P) - k.depthOf([b[0], b[1], 0], P));

  const bg = [];
  const fg = [];

  function put(name, ref, svg, shapes = [], { bias = 0, piece = "rig", ...rest } = {}) {
    return R.put({ name, at: ref, bias, piece, svg, shapes, ...rest });
  }

  function slab(name, plan, z, h, style = {}, { steps = 4, bevel = 0.6, seamZ = null, extra = "", inner = "", bias = 0, ground = false, piece = "rig", attrs = "" } = {}) {
    const shape = R.solid(A.slab(plan, z, h, { name, ground }, steps));
    const seamMarkup = seamZ !== null ? Ln(k.sideSeam(plan, seamZ, P, steps), { tone: "faint" }) : "";
    const raw = S(k.slabOf(plan, z, h, P, steps, bevel), { tone: "mid", ...style, inner: seamMarkup + inner }) + extra;
    const svg = attrs ? `<g ${attrs}>${raw}</g>` : raw;
    return put(name, [plan.x + plan.w / 2, plan.y + plan.d / 2, z + h / 2], svg, [shape], { bias, piece });
  }

  function cyl(name, cx, cy, r, z, h, style = {}, { steps = 32, bevel = 0, seamZs = [], knurlCount = 0, knurlInset = 0.35, extra = "", inner = "", bias = 0, ground = false, piece = "rig", attrs = "" } = {}) {
    const shape = R.solid(A.cylinder(cx, cy, r, z, h, { name, ground }));
    const seams = seamZs.length ? Ln(seamZs.map((sz) => k.sideArc(cx, cy, r, sz, P, Math.max(16, Math.round(steps * 0.75)))).join(""), { tone: "faint" }) : "";
    const knurls = knurlCount > 0 ? Ln(k.knurl(cx, cy, r, z, z + h, knurlCount, P, knurlInset), { tone: "lo" }) : "";
    const raw = S(k.cylinder(cx, cy, r, z, h, P, steps, bevel), { tone: "mid", ...style, inner: seams + inner }) + knurls + extra;
    const svg = attrs ? `<g ${attrs}>${raw}</g>` : raw;
    return put(name, [cx, cy, z + h / 2], svg, [shape], { bias, piece });
  }

  function benchPlate(PLATE, PLATE_H = 12, FOOT_H = 5) {
    bg.push(`<path class="iso-halo" d="${k.haloOf(PLATE, -PLATE_H - FOOT_H, PLATE_H, P)}"/>`);
    byDepth(k.corners(PLATE, 22)).forEach(([fx, fy], idx) => {
      cyl(`stand.flange${idx}`, fx, fy, 7, -PLATE_H - FOOT_H, 1.6, { tone: "lo" }, { steps: 28, ground: true });
      cyl(`stand.foot${idx}`, fx, fy, 5.4, -PLATE_H - FOOT_H + 1.6, FOOT_H - 1.6, { tone: "mid" }, { steps: 28, ground: true });
    });
    const screws = k.corners(PLATE, 10);
    const topDecor =
      Ln(k.planOutline(k.insetPlan(PLATE, 5), 0, P, 8), { tone: "lo" }) +
      Ln(screws.map(([sx, sy]) => k.ring(sx, sy, 2.2, 0, P, 16)).join(""), { tone: "lo" }) +
      Dots(screws.map(([sx, sy]) => at([sx, sy, 0])), { size: 0.5 });
    slab("stand.plate", PLATE, -PLATE_H, PLATE_H, { tone: "mid" }, {
      steps: 8,
      bevel: 1.6,
      seamZ: -PLATE_H / 2,
      extra: topDecor,
      ground: true,
    });
  }

  function rulerStrip(name, strip, z = 0, h = 0.6, { step = 4, every = 5 } = {}) {
    const ticks = k.topTicks(strip.x + 5, strip.x + strip.w - 5, step, every, strip.y + 0.6, z + h, [1.8, 3.4], P);
    const extra =
      Ln(ticks.minor, { tone: "lo" }) +
      Ln(ticks.major, { tone: "mid" }) +
      Dots([at([strip.x + 2.2, strip.y + strip.d / 2, z + h]), at([strip.x + strip.w - 2.2, strip.y + strip.d / 2, z + h])], { size: 0.45 });
    return slab(name, strip, z, h, { tone: "lo", crease: "none" }, { steps: 3, bevel: 0, extra, bias: 0.05 });
  }

  function labelPlate(name, plan, z = 0, h = 0.8, { text = "", rules = [26, 18] } = {}) {
    const border = Ln(k.planOutline(k.insetPlan(plan, 1.5), z + h, P, 3), { tone: "faint" });
    const content = text
      ? k.faceTextSvg(k.topMatrix([plan.x + 4, plan.y + plan.d - 2.4], z + h, P, "x"), text, { size: 2.8, tone: "lo" })
      : Ln(
          rules
            .map((rw, idx) =>
              k.lineOnTop(
                [plan.x + 4, plan.y + 2.8 + idx * 2.8],
                [plan.x + 4 + Math.min(rw, plan.w - 10), plan.y + 2.8 + idx * 2.8],
                z + h,
                P,
              ),
            )
            .join(""),
          { tone: "lo", free: true },
        );
    const rivets = Dots(
      [at([plan.x + 2, plan.y + plan.d / 2, z + h]), at([plan.x + plan.w - 2, plan.y + plan.d / 2, z + h])],
      { size: 0.42 },
    );
    return slab(name, plan, z, h, { tone: "lo", crease: "none" }, { steps: 3, bevel: 0, extra: border + content + rivets, bias: 0.05 });
  }

  function knurledKnob(name, cx, cy, r, z, h, { count = 32, pointerAngle = 0, tone = "mid" } = {}) {
    const topZ = z + h;
    const dx = Math.cos(pointerAngle) * (r - 0.3);
    const dy = Math.sin(pointerAngle) * (r - 0.3);
    const extra =
      Ln(k.ring(cx, cy, r - 1.6, topZ, P, 24), { tone: "faint" }) +
      Ln(k.lineOnTop([cx, cy], [cx + dx, cy + dy], topZ, P), { tone: "hi" }) +
      Dots([at([cx, cy, topZ])], { size: 0.52, tone: "hi" });
    return cyl(name, cx, cy, r, z, h, { tone }, { steps: Math.max(28, count), bevel: 0.4, knurlCount: count, extra });
  }

  function dialGauge(name, cx, cy, R_dial, z, h, { count = 48, every = 6, needlePart = "needle", startTurn = 0 } = {}) {
    const topZ = z + h;
    const ticks = k.radialTicks(cx, cy, R_dial - 2.6, count, every, topZ, [1.2, 2.6], P);
    const extra =
      Ln(k.ring(cx, cy, R_dial - 2.0, topZ, P, 64), { tone: "lo" }) +
      Ln(ticks.minor, { tone: "lo" }) +
      Ln(ticks.major, { tone: "mid" }) +
      Ln(k.ring(cx, cy, 1.6, topZ, P, 16), { tone: "mid" });
    cyl(name, cx, cy, R_dial, z, h, { tone: "hi", crease: "lo" }, {
      steps: 64,
      bevel: 0.8,
      seamZs: [topZ - 3.2],
      knurlCount: 72,
      knurlInset: 0.3,
      extra,
    });
    const needleAt = (turn) => {
      const a = turn * Math.PI * 2;
      return k.lineOnTop(
        [cx - Math.sin(a) * 3.0, cy + Math.cos(a) * 3.0],
        [cx + Math.sin(a) * (R_dial - 3.8), cy - Math.cos(a) * (R_dial - 3.8)],
        topZ + 0.2,
        P,
      );
    };
    fg.push(
      `<path data-part="${needlePart}" class="iso-line" data-tone="lit" data-free="both" d="${needleAt(startTurn)}" style="stroke-width:1.1"/>`,
    );
    return { topZ, needleAt };
  }

  function cable(name, points, r = 0.55, { tone = "mid", bend = 3.2, maxLength = 14, bias = 0.05 } = {}) {
    const route = G.fillet(points, Math.max(bend, r * 2.6), 10, { P, tube: r });
    R.route(name, route, r, { limp: true, ends: [true, true], piece: "rig" });
    tubePieces(route, r, P, { maxLength, spacing: Math.max(0.6, Math.min(1.4, r)) }).forEach((piece, index) => {
      put(`${name}:${index}`, piece.mid, tubeSvg(piece, { tone }), [A.tube(piece.points, piece.radii)], {
        bias,
        route: name,
        chunk: index,
      });
    });
    [0, route.length - 1].forEach((ptIdx, endIdx) => {
      const end = route[ptIdx];
      const dotR = Math.max(0.55, r * KS * 0.95);
      put(
        `${name}.end${endIdx}`,
        end,
        Dots([at(end)], { size: dotR, tone: "hi" }),
        [A.ball(end, dotR / KS, { name: `${name}.end${endIdx}`, owner: name })],
        { bias: bias + 0.12 },
      );
    });
  }

  function assembleSvg({ width, height, label, extraDefs = "", extraOverlay = "" }) {
    A.settle(R, P);
    const sorted = [...R.items].sort((a, b) => a.key - b.key);
    A.auditOrExit(R, P);
    return k.figureSvg({
      width,
      height,
      label,
      body: [
        extraDefs,
        ...bg,
        ...sorted.map((item) => item.svg),
        ...fg,
        extraOverlay,
      ],
    });
  }

  function writePages({ slug, fig, title, hint, readout, keys, caption, width = 680, svg, extraCss = "", liveScript = "", ariaLabel = title }) {
    mkdirSync(PAGES_DIR, { recursive: true });
    const stageBody = `<div class="iso-stage" tabindex="0" role="slider" aria-label="${ariaLabel.replace(/"/g, "&quot;")}" aria-valuemin="0" aria-valuemax="100" aria-valuenow="0">${svg}</div>`;
    const plate = `<style>${EMBED_HOOK_CSS}${extraCss}</style>` + k.plateHtml({ fig, title, hint, readout, keys, caption, body: stageBody });
    const fullScript = kitScript() + "\n" + EMBED_HOOK_JS + "\n" + liveScript;

    for (const t of ["dark", "light"]) {
      const file = join(PAGES_DIR, `${slug}${t === "light" ? "-light" : ""}.html`);
      writeFileSync(
        file,
        k.pageHtml({
          title: `${fig} — ${title}`,
          theme: t,
          width,
          body: plate,
          script: fullScript,
        }),
      );
    }
    return {
      darkPath: join(PAGES_DIR, `${slug}.html`),
      lightPath: join(PAGES_DIR, `${slug}-light.html`),
      solids: R.solids.length,
      items: R.items.length,
    };
  }

  return { R, KS, at, S, Ln, Dots, byDepth, bg, fg, put, slab, cyl, benchPlate, rulerStrip, labelPlate, knurledKnob, dialGauge, cable, assembleSvg, writePages };
}
