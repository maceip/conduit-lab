// End-to-end checks for the three-pane verified-browser showcase.
// Same guarantee as the old site: every metric on the page must equal what is in
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

test("ratchet stats render from ratchet.json", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("ratchet-stats")).toContainText(String(vurl.verified));
  await expect(page.getByTestId("stat-verified functions")).toHaveText(String(vurl.verified));
  await expect(page.getByTestId("stat-trusted items")).toHaveText(String(trustedTotal));
  await expect(page.getByTestId("stat-re-verify time")).toHaveText(`${vurl.verify_seconds}s`);
  await expect(page.getByTestId("stat-WPT + diff tests")).toHaveText(
    `${vurl.tests_passed}/${vurl.tests_passed + vurl.tests_failed}`
  );
  await expect(page.getByTestId("trusted-count")).toHaveText(String(trustedTotal));
  await expect(page.getByTestId("load-error")).toHaveCount(0);
});

test("three panes are present with their familiarity levels", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByText("01 · What Verus is")).toBeVisible();
  await expect(page.getByText("02 Why no verified Linux")).toBeVisible();
  await expect(page.getByText("03 · Where we are")).toBeVisible();
  await expect(page.getByText("Verus: Rust that proves itself")).toBeVisible();
  await expect(page.getByText("We have verified kernels. Just not Linux.")).toBeVisible();
  await expect(page.getByText("Where this engine actually stands")).toBeVisible();
});

test("pane 01 shows real vurl code and an interactive counterexample", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("verus-file").first()).toHaveText("browser/url/src/percent.rs");
  // the illustrative failure opens with its Z3 counterexample inlay expanded
  await expect(page.getByTestId("inlay-state-4")).toHaveText("failed");
  await expect(page.getByTestId("inlay-4")).toContainText("0x46");
  // clicking a collapsed verified glyph in the real-code editor expands its inlay
  await page.getByTestId("obligation-14").first().click();
  await expect(page.getByTestId("inlay-state-14")).toHaveText("verified");
});

test("pane 02 scale comparison and systems table", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("scale-sel4")).toHaveText("8,700 LOC");
  await expect(page.getByTestId("scale-vurl")).toHaveText(`${vurl.source_lines.toLocaleString("en-US")} LOC`);
  await expect(page.getByTestId("systems-table").locator("tbody tr")).toHaveCount(9);
});

test("pane 03 CVE grid, tallies, vjs status and tradeoffs", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByTestId("packet-count")).toHaveText("20 CVEs");
  await expect(page.getByTestId("coverage-tally")).toContainText("13/20");
  await expect(page.getByTestId("coverage-tally")).toContainText("3/20");
  await expect(page.getByTestId("coverage-tally")).toContainText("4/20");
  const vjsRows = page.getByTestId("vjs-table").locator("tbody tr");
  await expect(vjsRows).toHaveCount(9);
  for (const t of await vjsRows.locator("td:last-child").allTextContents()) expect(t).toBe("design");
  await expect(page.getByTestId("tradeoffs-table").locator("tbody tr")).toHaveCount(9);
  await expect(page.getByTestId("dag-summary")).toContainText("13 obligations");
  await expect(page.getByTestId("fuel-theorem")).toContainText("Unsupported(f)");
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
  await expect(page.getByTestId("trusted-count")).toHaveText("not recorded");
});