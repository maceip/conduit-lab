// End-to-end checks for the CONDUIT verified-browser GitHub Pages site.
// Every live metric must equal browser/ratchet.json and data/stats.json — zero hand-typed
// numbers, explicit errors on missing telemetry, verified interactive controls and layout geometry.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const root = path.join(__dirname, "..");
const ratchet = JSON.parse(fs.readFileSync(path.join(root, "browser", "ratchet.json"), "utf8"));
const stats = JSON.parse(fs.readFileSync(path.join(root, "data", "stats.json"), "utf8"));
const totals = ratchet.totals;
const totalTrusted = Object.values(totals.trusted).reduce((a, b) => a + b, 0);
const totalDiffCases = ratchet.test262_suites.reduce(
  (acc, s) => acc + (typeof s.differential_cases === "number" ? s.differential_cases : 0),
  0
);

test("built HTML, app JS, and site source contain no hard-coded ratchet results", async () => {
  const html = fs.readFileSync(path.join(root, "dist", "index.html"), "utf8");
  const assetsDir = path.join(root, "dist", "assets");
  const appJsFiles = fs
    .readdirSync(assetsDir)
    .filter((f) => f.endsWith(".js") && !f.startsWith("vendor-"))
    .map((f) => ({ name: `dist/assets/${f}`, text: fs.readFileSync(path.join(assetsDir, f), "utf8") }));
  expect(appJsFiles.length, "app JS bundle must exist").toBeGreaterThan(0);

  const srcDir = path.join(root, "site", "src");
  const walkSrc = (dir) =>
    fs.readdirSync(dir, { withFileTypes: true }).flatMap((ent) => {
      const full = path.join(dir, ent.name);
      return ent.isDirectory() ? walkSrc(full) : [{ name: path.relative(root, full), text: fs.readFileSync(full, "utf8") }];
    });
  const checkedFiles = [{ name: "dist/index.html", text: html }, ...appJsFiles, ...walkSrc(srcDir)];

  const forbidden = [
    String(totals.verified),
    totals.verified.toLocaleString("en-US"),
    String(totals.verify_seconds),
    String(totals.source_lines),
    totals.source_lines.toLocaleString("en-US"),
  ];
  for (const v of forbidden) {
    for (const file of checkedFiles) {
      expect(file.text, `${file.name} must not contain hard-coded ${v}`).not.toContain(v);
    }
  }
});

test("scoreboard renders live 11-crate totals and enforces adjacent pill density <= 2", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("stat-verified queries")).toHaveText(totals.verified.toLocaleString("en-US"));
  await expect(page.getByTestId("stat-trusted items")).toHaveText(String(totalTrusted));
  await expect(page.getByTestId("stat-re-verify time")).toHaveText(`${totals.verify_seconds}s`);
  await expect(page.getByTestId("stat-crate tests")).toHaveText(
    `${totals.tests_passed}/${totals.tests_passed + totals.tests_failed}`
  );
  await expect(page.getByTestId("ratchet-stats")).toContainText(`verus ${ratchet.verus}`);
  await expect(page.getByTestId("ratchet-stats")).toContainText(`${totals.crates} crates`);
  await expect(page.getByTestId("ratchet-stats")).toContainText(
    `${totals.functions_by_mode.exec.toLocaleString("en-US")} exec · ${totals.functions_by_mode.proof.toLocaleString("en-US")} proof fns`
  );
  await expect(page.getByTestId("inputs-digest")).toHaveText(ratchet.inputs_sha256.slice(0, 12));
  await expect(page.getByTestId("load-error")).toHaveCount(0);

  // Label density check: provenance pill stack must stay <= 2 adjacent pills
  const pillCount = await page.getByTestId("provenance-pills").locator(".ch-digest-pill").count();
  expect(pillCount, "adjacent provenance pills must be <= 2").toBeLessThanOrEqual(2);

  // Verify verus revision text is not clipped horizontally inside its digest pill
  const verusClipped = await page
    .getByTestId("provenance-pills")
    .locator(".ch-digest-left")
    .first()
    .evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(verusClipped, "verus revision pill must not clip").toBeLessThanOrEqual(2);
});

test("all rendered hero and brand images load cleanly", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("hero-visual").locator("img")).toBeVisible();

  const imgStates = await page.locator("img").evaluateAll((imgs) =>
    imgs.map((img) => ({
      src: img.getAttribute("src"),
      complete: img.complete,
      naturalWidth: img.naturalWidth,
    }))
  );
  expect(imgStates.length).toBeGreaterThanOrEqual(3);
  for (const img of imgStates) {
    expect(img.complete, `${img.src} must finish loading`).toBe(true);
    expect(img.naturalWidth, `${img.src} must have naturalWidth > 0`).toBeGreaterThan(0);
  }
});

test("sections lead with formal verification, navigation matches order, and copy has zero stale claims", async ({
  page,
}) => {
  await page.goto("/");
  const ids = await page.locator("main > section").evaluateAll((ss) => ss.map((s) => s.id));
  expect(ids).toEqual(["proofs", "arch", "ratchet", "scope", "coverage"]);
  const navTargets = await page.locator(".ch-nav a").evaluateAll((as) => as.map((a) => a.getAttribute("href")));
  expect(navTargets).toEqual(ids.map((id) => `#${id}`));

  const lede = page.getByTestId("lede");
  await expect(lede).toContainText("Prove they cannot exist");
  await expect(lede).toContainText("13 of the last 20 Chrome zero-days");
  await expect(lede).toContainText(`${totals.crates} crates`);

  const body = await page.locator("body").innerText();
  for (const stale of [
    "vjs is 0% built",
    "Only vurl is implemented",
    "Bytecode + simulation proof deferred to J7",
    "Honesty clause",
    "Apple Silicon",
  ]) {
    expect(body, `stale phrase must not appear: ${stale}`).not.toContain(stale);
  }
});

test("section 1 (#proofs): 4-state Verus workbench, fix-typo action, and live 11-crate proof explorer", async ({
  page,
}) => {
  await page.goto("/");
  await expect(page.getByTestId("verus-file")).toHaveText("browser/url/src/percent.rs");
  await expect(page.getByTestId("inlay-state-8")).toHaveText("verified");

  const overflow = await page
    .getByTestId("verus-code-workbench")
    .evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(overflow, "Verus code workbench must not overflow horizontally").toBeLessThanOrEqual(2);

  // Switch to Counterexample -> verify Z3 model -> click Fix Typo button back to Verified
  await page.getByTestId("state-failed").click();
  await expect(page.getByTestId("inlay-state-4")).toHaveText("failed");
  await expect(page.getByTestId("z3-counterexample")).toContainText('0x46 ("F")');
  await page.getByTestId("btn-fix-typo").click();
  await expect(page.getByTestId("verus-file")).toHaveText("browser/url/src/percent.rs");
  await expect(page.getByTestId("inlay-state-8")).toHaveText("verified");

  // Switch to Timeout & Admit states
  await page.getByTestId("state-timeout").click();
  await expect(page.getByTestId("inlay-state-4")).toHaveText("timeout");
  await page.getByTestId("state-admit").click();
  await expect(page.getByTestId("inlay-state-5")).toHaveText("admit");

  // Live 11-crate proof source explorer fetches real .rs files
  await page.getByTestId("tab-live-proofs").click();
  await expect(page.getByTestId("live-proof-file")).toHaveText("browser/url/src/ipv6.rs");
  await expect(page.getByTestId("live-proof-source")).toContainText("spec_hex_run");

  await page.getByTestId("proof-crate-vjs_vm").click();
  await expect(page.getByTestId("live-proof-file")).toHaveText("browser/vjs-vm/src/compiler_proof.rs");
  await expect(page.getByTestId("live-proof-source")).toContainText("CompCert");
});

test("section 2 (#arch): trust-boundary diagram fits cleanly without overflow", async ({ page }) => {
  await page.goto("/");
  const diagram = page.getByTestId("shim-diagram");
  await expect(diagram).toBeVisible();
  await expect(diagram).toContainText("VERIFIED SECURITY KERNEL");
  await expect(diagram).toContainText("Typed Vest IPC");
  const overflow = await diagram.evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(overflow, "architecture diagram must not overflow horizontally").toBeLessThanOrEqual(2);
});

test("section 3 (#ratchet): 11-crate ledger, scope boundary, and collapsible engineering drawers", async ({
  page,
}) => {
  await page.goto("/");
  const cratesTable = page.getByTestId("crates-table");
  await expect(cratesTable.locator("tbody tr")).toHaveCount(ratchet.crates.length);
  for (const c of ratchet.crates) {
    await expect(cratesTable).toContainText(c.name);
  }

  // Disclosure card stays accurate and never truncates
  const card = page.getByTestId("honesty-card");
  await expect(card).toContainText(`${totals.crates} crates`);
  await expect(card).toContainText("non-interference theorems");
  const clipped = await card.evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(clipped, "scope disclosure card must not truncate").toBeLessThanOrEqual(2);

  // Secondary engineering deep-dives are collapsed by default to keep the page uncluttered
  const benchDrawer = page.getByTestId("bench-drawer");
  const dagDrawer = page.getByTestId("dag-drawer");
  const tradeoffsDrawer = page.getByTestId("tradeoffs-drawer");
  await expect(benchDrawer).not.toHaveAttribute("open", "");
  await expect(dagDrawer).not.toHaveAttribute("open", "");
  await expect(tradeoffsDrawer).not.toHaveAttribute("open", "");

  // Expand benchmarks & conformance drawer
  await benchDrawer.locator("summary").click();
  await expect(benchDrawer).toHaveAttribute("open", "");
  const benchCard = page.getByTestId("vm-benchmarks");
  await expect(benchCard).toContainText(`${ratchet.vm_benchmarks_geomean_speedup}×`);
  const benchOverflow = await benchCard
    .locator(".ch-table-card")
    .evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(benchOverflow, "VM benchmark table must fit without horizontal clipping").toBeLessThanOrEqual(2);

  const suites = page.getByTestId("suites-table");
  await expect(suites.locator("tbody tr")).toHaveCount(ratchet.test262_suites.length);
  await expect(suites).toContainText(totalDiffCases.toLocaleString("en-US"));
  await expect(page.getByTestId("fuel-theorem")).toContainText("Unsupported(f)");

  // Expand obligation DAG drawer and verify zero node overlap + interactive node inspection
  await dagDrawer.locator("summary").click();
  await expect(dagDrawer).toHaveAttribute("open", "");
  await expect(page.getByTestId("dag-summary")).toContainText("13 obligations");

  const dagOverlap = await page.locator(".ch-dag-node").evaluateAll((nodes) => {
    const rects = nodes.map((n) => n.getBoundingClientRect());
    for (let i = 0; i < rects.length; i++) {
      for (let j = i + 1; j < rects.length; j++) {
        const a = rects[i];
        const b = rects[j];
        const overlaps = !(a.right <= b.left || b.right <= a.left || a.bottom <= b.top || b.bottom <= a.top);
        if (overlaps) return { i, j, a, b };
      }
    }
    return null;
  });
  expect(dagOverlap, "Proof DAG nodes must never overlap").toBeNull();

  await page.getByTestId("dag-node-ipv4_parse").click();
  await expect(page.getByTestId("dag-inspector")).toContainText("ipv4_parse");
  await expect(page.getByTestId("dag-inspector")).toContainText("ipv4_number");

  // Expand tradeoffs drawer and verify all 9 architectural decisions render cleanly
  await tradeoffsDrawer.locator("summary").click();
  await expect(tradeoffsDrawer).toHaveAttribute("open", "");
  const tradeoffs = page.getByTestId("tradeoffs");
  await expect(tradeoffs.locator("tbody tr")).toHaveCount(9);
  await expect(tradeoffs).toContainText("What we give up");
});

test("section 4 (#scope): live scale bars and prior-art table fit cleanly", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("scale-sel4")).toHaveText("8,700 LOC");
  await expect(page.getByTestId("scale-conduit")).toHaveText(`${totals.source_lines.toLocaleString("en-US")} LOC`);

  const table = page.getByTestId("systems-table");
  await expect(table.locator("tbody tr")).toHaveCount(9);
  const wrapOverflow = await table.locator("..").evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(wrapOverflow, "prior-art table must fit its column").toBeLessThanOrEqual(2);
});

test("section 5 (#coverage): 20-CVE appendix is collapsed at bottom by default and interactive on expand", async ({
  page,
}) => {
  await page.goto("/");
  const cveDrawer = page.getByTestId("cve-drawer");
  await expect(cveDrawer).not.toHaveAttribute("open", "");
  await expect(page.getByTestId("cve-table")).not.toBeVisible();

  // Expand CVE appendix drawer
  await cveDrawer.locator("summary").click();
  await expect(cveDrawer).toHaveAttribute("open", "");
  await expect(page.getByTestId("packet-count")).toHaveText("20 CVEs");
  await expect(page.locator("#coverage")).toContainText("13/20");
  await expect(page.locator("#coverage")).toContainText("3/20");
  await expect(page.locator("#coverage")).toContainText("4/20");

  // Default selected CVE is first row
  const detail = page.getByTestId("cve-detail");
  await expect(detail).toContainText("CVE-2026-125350");
  await expect(detail).toContainText("157.0.8103.50");

  // Filter to graphics gap (4 CVEs) and inspect Skia CVE
  await page.getByTestId("cve-filter-graphics").click();
  await expect(page.getByTestId("packet-count")).toHaveText("4 CVEs");
  await expect(page.getByTestId("cve-table").locator("tbody tr")).toHaveCount(4);
  await page.getByTestId("cve-row-CVE-2026-3909").click();
  await expect(detail).toContainText("CVE-2026-3909");
  await expect(detail).toContainText("Outside formal verification");

  // Filter back to all
  await page.getByTestId("cve-filter-all").click();
  await expect(page.getByTestId("cve-table").locator("tbody tr")).toHaveCount(20);
});

test("theme switch toggles dark/light mode cleanly and persists", async ({ page }) => {
  await page.goto("/");
  await expect(page.locator("html")).toHaveAttribute("data-theme", "dark");
  await page.getByTestId("theme-switch").click();
  await expect(page.locator("html")).toHaveAttribute("data-theme", "light");
  await page.reload();
  await expect(page.locator("html")).toHaveAttribute("data-theme", "light");
});

test("provenance footer and staged local assets resolve with HTTP 200", async ({ page, request }) => {
  await page.goto("/");
  const footer = page.getByTestId("provenance-footer");
  await expect(footer).toContainText("browser/ratchet.json");
  await expect(footer).toContainText("data/stats.json");
  for (const h of [
    "browser/ratchet.json",
    "data/stats.json",
    "irrigation.html",
    "v8-anatomy.html",
    "v8-iso/pages/fig-01-isolate.html",
    "v8-iso/pages/fig-02-pointer-tagging.html",
    "v8-iso/pages/fig-03-hidden-classes.html",
    "v8-iso/pages/fig-04-parser.html",
    "v8-iso/pages/fig-05-ignition.html",
    "v8-iso/pages/fig-06-torque-csa.html",
    "v8-iso/pages/fig-07-old-space.html",
    "v8-iso/pages/fig-08-new-space.html",
    "v8-iso/pages/showcase-01-jet-engine.html",
    "v8-iso/pages/showcase-02-sports-car.html",
    "v8-iso/pages/showcase-03-cruise-ship.html",
    "styles.css",
    "assets/conduit-favicon.png",
    "assets/conduit-mark.png",
    "assets/hero-modules-backdrop.webp",
    "assets/hw-kernel.webp",
    "assets/hw-prover.webp",
    "assets/hw-synthesis.webp",
    "assets/hw-waveform.webp",
    "assets/sticker-shield.webp",
    "assets/sticker-scroll.webp",
    "assets/sticker-knot.webp",
    "assets/sticker-lock.webp",
    "assets/conduit-arch-iso.webp",
    "assets/conduit-banner-wide.jpg",
    "assets/fonts/archivo-latin.woff2",
    "assets/fonts/manrope-latin.woff2",
    "assets/fonts/jetbrains-mono-latin.woff2",
    "data/examples/browser-vjs_vm-compiler_proof.rs",
    "data/logs/browser-vjs_vm.log",
  ]) {
    expect((await request.get(`/${h}`)).status(), h).toBe(200);
  }
});

test("missing ratchet.json and stats.json show load-error and not recorded", async ({ page }) => {
  await page.route("**/browser/ratchet.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.route("**/data/stats.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.goto("/");
  await expect(page.getByTestId("load-error")).toBeVisible();
  await expect(page.getByTestId("load-error")).toContainText("HTTP 404");
  await expect(page.getByTestId("stat-verified queries")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-trusted items")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-re-verify time")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-crate tests")).toHaveText("not recorded");
  await expect(page.getByTestId("scale-conduit")).toHaveText("not recorded");
  await expect(page.getByTestId("crates-table-missing")).toContainText("not recorded");
});

// Each of these alone must turn the crate's dot, its count, the workspace total and (for vurl) the DAG red.
for (const [why, mutate] of [
  ["Verus exits non-zero", (c) => (c.verify_exit = 1)],
  ["Verus reports errors", (c) => (c.errors = 1)],
  ["not verified under --no-cheating", (c) => (c.no_cheating = false)],
  ["report predates the no_cheating field", (c) => delete c.no_cheating],
  ["a trust marker is present", (c) => (c.trusted.axiom = 1)],
  ["a vacuous contract is present", (c) => (c.vacuous_requires = 1)],
  ["cargo test exits non-zero", (c) => (c.tests_exit = 101)],
  ["a test failed", (c) => (c.tests_failed = 1)],
]) {
  test(`vurl is not shown as verified when ${why}`, async ({ page }) => {
    const row = page.getByTestId("crates-table").locator("tbody tr").first();
    const total = page.getByTestId("crates-table").locator("tfoot tr");
    await page.goto("/");
    await expect(row.locator(".ch-status-dot")).toHaveAttribute("data-tone", "proved");
    await expect(total).toContainText("All crates verified");
    const dagBefore = await page.locator(".ch-dag-node").evaluateAll((ns) => ns.map((n) => n.outerHTML));

    const changed = JSON.parse(JSON.stringify(ratchet));
    mutate(changed.crates[0]);
    await page.route("**/browser/ratchet.json", (r) => r.fulfill({ json: changed }));
    await page.reload();
    await expect(row).toContainText("vurl");
    await expect(row.locator(".ch-status-dot")).toHaveAttribute("data-tone", "fail");
    await expect(total).toContainText("Some crates fail a proof, trust, or test check");
    const dagAfter = await page.locator(".ch-dag-node").evaluateAll((ns) => ns.map((n) => n.outerHTML));
    expect(dagAfter, "DAG must stop showing its nodes as verified").not.toEqual(dagBefore);
  });
}
