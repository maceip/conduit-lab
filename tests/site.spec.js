// End-to-end checks for the verified-browser showcase (single-scroll layout).
// Every metric on the page must equal what is in browser/ratchet.json and
// data/stats.json — nothing hand-typed, errors instead of guesses.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const root = path.join(__dirname, "..");
const ratchet = JSON.parse(fs.readFileSync(path.join(root, "browser", "ratchet.json"), "utf8"));
const stats = JSON.parse(fs.readFileSync(path.join(root, "data", "stats.json"), "utf8"));
const totals = ratchet.totals;
const totalTrusted = Object.values(totals.trusted).reduce((a, b) => a + b, 0);

test("built HTML and JS contain no hard-coded ratchet results", async () => {
  const html = fs.readFileSync(path.join(root, "dist", "index.html"), "utf8");
  const assetsDir = path.join(root, "dist", "assets");
  const jsFiles = fs
    .readdirSync(assetsDir)
    .filter((f) => f.endsWith(".js"))
    .map((f) => ({ name: f, text: fs.readFileSync(path.join(assetsDir, f), "utf8") }));

  const forbidden = [
    String(totals.verified),
    String(totals.verify_seconds),
    String(totals.source_lines),
  ];
  for (const v of forbidden) {
    expect(html, `dist/index.html must not contain ${v}`).not.toContain(v);
    for (const jf of jsFiles) {
      expect(jf.text, `dist/assets/${jf.name} must not contain ${v}`).not.toContain(v);
    }
  }
});

test("scoreboard renders live 11-crate totals and respects chip density <= 2", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("stat-verified functions")).toHaveText(String(totals.verified));
  await expect(page.getByTestId("stat-trusted items")).toHaveText(String(totalTrusted));
  await expect(page.getByTestId("stat-re-verify time")).toHaveText(`${totals.verify_seconds}s`);
  await expect(page.getByTestId("stat-crate tests")).toHaveText(
    `${totals.tests_passed}/${totals.tests_passed + totals.tests_failed}`
  );
  await expect(page.getByTestId("ratchet-stats")).toContainText(`verus ${ratchet.verus}`);
  await expect(page.getByTestId("ratchet-stats")).toContainText(`${totals.crates} crates`);
  await expect(page.getByTestId("load-error")).toHaveCount(0);

  // Label density check: no container may stack 3+ adjacent .wb-chip or .pill badges
  const maxChipsInContainer = await page.evaluate(() => {
    const containers = Array.from(document.querySelectorAll(".wb-chips, .pills"));
    return containers.reduce((max, el) => {
      const count = el.querySelectorAll(".wb-chip, .pill").length;
      return Math.max(max, count);
    }, 0);
  });
  expect(maxChipsInContainer, "adjacent chips/badges must be <= 2").toBeLessThanOrEqual(2);
});

test("all illustrations and icons load cleanly with naturalWidth > 0", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("hero-banner").locator("img")).toBeVisible();
  await expect(page.getByTestId("iso-architecture").locator("img")).toBeVisible();
  await expect(page.getByTestId("arch-cards").locator("article")).toHaveCount(4);

  const imgStates = await page.locator("img").evaluateAll((imgs) =>
    imgs.map((img) => ({
      src: img.getAttribute("src"),
      complete: img.complete,
      naturalWidth: img.naturalWidth,
    }))
  );
  expect(imgStates.length).toBeGreaterThanOrEqual(7);
  for (const img of imgStates) {
    expect(img.complete, `${img.src} must finish loading`).toBe(true);
    expect(img.naturalWidth, `${img.src} must have naturalWidth > 0`).toBeGreaterThan(0);
  }
});

test("single scroll: no pane layout, chapters in familiarity order, plain copy", async ({ page }) => {
  await page.goto("/");
  await expect(page.locator("ix-pane-layout")).toHaveCount(0);
  await expect(page.locator("ix-blind")).toHaveCount(0);
  const ids = await page.locator("main section").evaluateAll((ss) => ss.map((s) => s.id));
  expect(ids).toEqual(["coverage", "verus", "why", "arch", "status"]);
  const navTargets = await page.locator(".wb-nav a").evaluateAll((as) => as.map((a) => a.getAttribute("href")));
  expect(navTargets).toEqual(ids.map((id) => `#${id}`));
  const lede = page.getByTestId("lede");
  await expect(lede).toContainText("Of the last 20 Chrome bugs");
  await expect(lede).toContainText("13 were in V8");
  await expect(lede).toContainText(`${totals.crates} crates`);
  const body = await page.locator("body").innerText();
  for (const phrase of ["Honesty clause", "First contact", "The other half", "project's bet", "Only vurl is implemented"]) {
    expect(body, `stale/marketing phrase removed: ${phrase}`).not.toContain(phrase);
  }
});

test("section 02: state cards switch the editor; wide column does not clip code", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("verus-file")).toHaveText("browser/url/src/percent.rs");
  await expect(page.getByTestId("inlay-state-10")).toHaveText("verified");
  const overflow = await page.locator(".ix-verus-body").evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(overflow, "code column must not scroll horizontally").toBeLessThanOrEqual(2);
  await page.getByTestId("state-failed").click();
  await expect(page.getByTestId("inlay-state-4")).toHaveText("failed");
  await expect(page.getByTestId("inlay-4")).toContainText("0x46");
  await page.getByTestId("state-timeout").click();
  await expect(page.getByTestId("inlay-state-8")).toHaveText("timeout");
  await page.getByTestId("state-admit").click();
  await expect(page.getByTestId("inlay-state-9")).toHaveText("admit");
});

test("section 03: live scale bars, reasons disclosures, prior-art table without inner scroll", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("scale-sel4")).toHaveText("8,700 LOC");
  await expect(page.getByTestId("scale-conduit")).toHaveText(`${totals.source_lines.toLocaleString("en-US")} LOC`);
  await expect(page.getByTestId("reasons").locator("details")).toHaveCount(4);
  const table = page.getByTestId("systems-table");
  await expect(table.locator("tbody tr")).toHaveCount(9);
  const wrapOverflow = await table.locator("..").evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(wrapOverflow, "prior-art table must fit its column").toBeLessThanOrEqual(2);
});

test("section 05: 11-crate table, J0-J7 live rows, VM benchmarks, conformance suites, DAG and honesty card", async ({ page }) => {
  await page.goto("/");
  const cratesTable = page.getByTestId("crates-table");
  await expect(cratesTable.locator("tbody tr")).toHaveCount(ratchet.crates.length);
  for (const c of ratchet.crates) {
    await expect(cratesTable).toContainText(c.name);
  }

  const vjsRows = page.getByTestId("vjs-rows");
  await expect(vjsRows.locator("details")).toHaveCount(ratchet.j_steps.length);
  for (const step of ratchet.j_steps) {
    await expect(vjsRows).toContainText(`${step.test262_passed}/${step.test262_total}`);
  }

  await expect(page.getByTestId("vm-benchmarks")).toContainText(`${ratchet.vm_benchmarks_geomean_speedup}×`);
  await expect(page.getByTestId("suites-table").locator("tbody tr")).toHaveCount(ratchet.test262_suites.length);
  await expect(page.getByTestId("modules").locator("details")).toHaveCount(3);
  await expect(page.getByTestId("tradeoffs").locator("details")).toHaveCount(9);
  await expect(page.getByTestId("fuel-theorem")).toContainText("Unsupported(f)");
  await expect(page.getByTestId("dag-summary")).toContainText("13 obligations");

  const card = page.getByTestId("honesty-card");
  await expect(card).toContainText(`${totals.crates} crates`);
  await expect(card).toContainText("kernel theorems");
  const clipped = await card.evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(clipped, "honesty card must not truncate").toBeLessThanOrEqual(2);

  await page.getByTestId("tradeoffs").locator("details").nth(1).locator("summary").click();
  await expect(page.getByTestId("tradeoffs").locator("details").nth(1)).toContainText("Given up");
});

test("coverage: full-width grid, tally, in-place CVE detail", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("packet-count")).toHaveText("20 CVEs");
  await expect(page.getByTestId("coverage-tally")).toContainText("13/20");
  await expect(page.getByTestId("coverage-tally")).toContainText("3/20");
  await expect(page.getByTestId("coverage-tally")).toContainText("4/20");
  await page.locator('[role="row"][aria-rowindex="1"]').click();
  const detail = page.getByTestId("cve-detail");
  await expect(detail).toContainText("CVE-2026-125350");
  await expect(detail).toContainText("This engine's answer");
  await page.locator('[role="row"][aria-rowindex="6"]').click();
  await expect(detail).toContainText("CVE-2026-3909");
  await expect(detail).toContainText("Not covered by proofs");
});

test("theme toggle switches the iX color schema", async ({ page }) => {
  await page.goto("/");
  await expect(page.locator("html")).toHaveAttribute("data-ix-color-schema", "dark");
  await page.locator("ix-toggle").click();
  await expect(page.locator("html")).toHaveAttribute("data-ix-color-schema", "light");
});

test("provenance footer and local data links resolve", async ({ page, request }) => {
  await page.goto("/");
  const footer = page.getByTestId("provenance-footer");
  await expect(footer).toContainText("browser/ratchet.json");
  await expect(footer).toContainText("data/stats.json");
  for (const h of [
    "browser/ratchet.json",
    "data/stats.json",
    "irrigation.html",
    "styles.css",
    "assets/conduit-favicon.png",
    "assets/conduit-banner-wide.jpg",
    "assets/conduit-iso-architecture.jpg",
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
  await expect(page.getByTestId("stat-verified functions")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-trusted items")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-re-verify time")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-crate tests")).toHaveText("not recorded");
  await expect(page.getByTestId("scale-conduit")).toHaveText("not recorded");
  await expect(page.getByTestId("crates-table-missing")).toContainText("not recorded");
});
