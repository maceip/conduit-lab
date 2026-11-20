// End-to-end checks: every number on the page must equal what is in data/stats.json.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const stats = JSON.parse(fs.readFileSync(path.join(__dirname, "..", "data", "stats.json"), "utf8"));
const benches = stats.lean.benchmarks;
const attempted = benches.filter((b) => !["skipped_mathlib", "no_lakefile"].includes(b.status));
const passed = attempted.filter((b) => b.status === "passed");

test("index.html contains no hard-coded results", async () => {
  const html = fs.readFileSync(path.join(__dirname, "..", "index.html"), "utf8");
  for (const v of [String(stats.verus.vstd.verified), "4.16.0", "1.100.0", "4.29.1", "32 jobs"]) {
    expect(html, `index.html must not contain ${v}`).not.toContain(v);
  }
});

test("stats strip and chips render from stats.json", async ({ page }) => {
  await page.goto("/");
  const strip = page.getByTestId("stats");
  await expect(strip).toContainText(`${stats.verus.vstd.verified}vstd obligations verified`);
  await expect(strip).toContainText(`${passed.length}/${attempted.length}`);
  await expect(strip).toContainText(`(${benches.length} total)`);
  const z3 = stats.toolchains.z3.match(/version ([\d.]+)/)[1];
  await expect(page.getByTestId("chips")).toContainText(`Z3 ${z3}`);
  await expect(page.locator("#load-error")).toBeHidden();
});

test("provenance tables list every repo and toolchain", async ({ page }) => {
  await page.goto("/");
  const repos = page.getByTestId("repos");
  for (const r of stats.repos) {
    await expect(repos).toContainText(r.name);
    await expect(repos).toContainText(r.commit.slice(0, 10));
  }
  const tc = page.getByTestId("toolchains");
  for (const v of Object.values(stats.toolchains)) if (v) await expect(tc).toContainText(v);
});

test("all evidence links resolve", async ({ page, request }) => {
  await page.goto("/");
  await expect(page.getByTestId("benchmarks").locator("tbody tr")).toHaveCount(benches.length);
  const hrefs = await page.locator("a.link").evaluateAll((as) => as.map((a) => a.getAttribute("href")));
  const local = [...new Set(hrefs.filter((h) => h && !h.startsWith("http")))];
  expect(local.length).toBeGreaterThan(benches.length / 2);
  for (const h of local) expect((await request.get(h)).status(), h).toBe(200);
});

test("example proof shows the verified source and result", async ({ page }) => {
  await page.goto("/");
  const ex = stats.verus.examples[0];
  await expect(page.getByTestId("example-result")).toContainText(`${ex.verified} verified, ${ex.errors} errors`);
  const src = fs.readFileSync(path.join(__dirname, "..", ex.source), "utf8");
  await expect(page.getByTestId("example-src")).toHaveText(src);
  await expect(page.getByTestId("qs-verus")).toHaveText(`verification results:: ${ex.verified} verified, ${ex.errors} errors`);
});

test("benchmark filters show exactly the matching rows", async ({ page }) => {
  await page.goto("/");
  const rows = page.getByTestId("benchmarks").locator("tbody tr");
  for (const status of new Set(benches.map((b) => b.status))) {
    const btn = page.locator(`#bench-filters button[data-f="${status}"]`);
    await btn.click();
    await expect(btn).toHaveAttribute("aria-pressed", "true");
    await expect(rows).toHaveCount(benches.filter((b) => b.status === status).length);
    for (const s of await rows.evaluateAll((rs) => rs.map((r) => r.dataset.status))) expect(s).toBe(status);
  }
  await page.locator('#bench-filters button[data-f="all"]').click();
  await expect(rows).toHaveCount(benches.length);
});

test("missing stats.json shows an error and no numbers", async ({ page }) => {
  await page.route("**/data/stats.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.goto("/");
  await expect(page.locator("#load-error")).toBeVisible();
  await expect(page.locator("#load-error")).toContainText("HTTP 404");
  await expect(page.getByTestId("stats")).toBeEmpty();
  await expect(page.getByTestId("chips")).toBeEmpty();
});
