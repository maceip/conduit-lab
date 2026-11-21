// End-to-end checks for the verified-browser showcase (v3 single-scroll layout).
// Same guarantee as before: every metric on the page must equal what is in
// browser/ratchet.json / data/stats.json — nothing hand-typed, errors instead of guesses.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const root = path.join(__dirname, "..");
const ratchet = JSON.parse(fs.readFileSync(path.join(root, "browser", "ratchet.json"), "utf8"));
const stats = JSON.parse(fs.readFileSync(path.join(root, "data", "stats.json"), "utf8"));
const vurl = ratchet.crates.find((c) => c.name === "vurl");
const trustedTotal = Object.values(vurl.trusted).reduce((a, b) => a + b, 0);

test("built index.html contains no hard-coded results", async () => {
  const html = fs.readFileSync(path.join(root, "dist", "index.html"), "utf8");
  for (const v of [String(vurl.verified), String(vurl.verify_seconds), String(vurl.source_lines)]) {
    expect(html, `dist/index.html must not contain ${v}`).not.toContain(v);
  }
});

test("scoreboard renders live ratchet metrics and pinned digests", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("stat-verified functions")).toHaveText(String(vurl.verified));
  await expect(page.getByTestId("stat-trusted items")).toHaveText(String(trustedTotal));
  await expect(page.getByTestId("stat-re-verify time")).toHaveText(`${vurl.verify_seconds}s`);
  await expect(page.getByTestId("stat-WPT + diff tests")).toHaveText(
    `${vurl.tests_passed}/${vurl.tests_passed + vurl.tests_failed}`
  );
  await expect(page.getByTestId("ratchet-stats")).toContainText("whatwg/url @4f461b81");
  await expect(page.getByTestId("load-error")).toHaveCount(0);
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
  const body = await page.locator("body").innerText();
  for (const phrase of ["Honesty clause", "First contact", "The other half", "project's bet"]) {
    expect(body, `marketing phrase removed: ${phrase}`).not.toContain(phrase);
  }
});

test("section 01: state cards switch the editor; wide column does not clip code", async ({ page }) => {
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

test("section 02: live scale bars, reasons disclosures, prior-art table without inner scroll", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("scale-sel4")).toHaveText("8,700 LOC");
  await expect(page.getByTestId("scale-vurl")).toHaveText(`${vurl.source_lines.toLocaleString("en-US")} LOC`);
  await expect(page.getByTestId("reasons").locator("details")).toHaveCount(4);
  const table = page.getByTestId("systems-table");
  await expect(table.locator("tbody tr")).toHaveCount(9);
  const wrapOverflow = await page.locator(".wb-table-wrap").evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(wrapOverflow, "prior-art table must fit its column").toBeLessThanOrEqual(2);
});

test("section 03: modules, vjs steps, tradeoffs, DAG and untruncated honesty card", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("modules").locator("details")).toHaveCount(3);
  await expect(page.getByTestId("vjs-rows").locator("details")).toHaveCount(9);
  await expect(page.getByTestId("tradeoffs").locator("details")).toHaveCount(9);
  await expect(page.getByTestId("fuel-theorem")).toContainText("Unsupported(f)");
  await expect(page.getByTestId("dag-summary")).toContainText("13 obligations");
  const card = page.getByTestId("honesty-card");
  await expect(card).toContainText("Only vurl is implemented");
  await expect(card).toContainText("design documents, not code");
  const clipped = await card.evaluate((el) => el.scrollWidth - el.clientWidth);
  expect(clipped, "honesty card must not truncate").toBeLessThanOrEqual(2);
  // a tradeoff disclosure opens to full stacked fields
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
  for (const h of ["browser/ratchet.json", "data/stats.json", "irrigation.html", "styles.css"]) {
    expect((await request.get(`/${h}`)).status(), h).toBe(200);
  }
});

test("missing ratchet.json shows an error and no guessed numbers", async ({ page }) => {
  await page.route("**/browser/ratchet.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.goto("/");
  await expect(page.getByTestId("load-error")).toBeVisible();
  await expect(page.getByTestId("load-error")).toContainText("HTTP 404");
  await expect(page.getByTestId("stat-verified functions")).toHaveText("not recorded");
  await expect(page.getByTestId("stat-trusted items")).toHaveText("not recorded");
  await expect(page.getByTestId("scale-vurl")).toHaveText("not recorded");
});