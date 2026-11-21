// End-to-end Playwright verification for the 10 interactive isometric V8 figures
// (5 wheresryan22/anatomy benchtop rigs + 5 MrBongoC/ai-iso-skill consoles),
// the standalone side-by-side gallery (v8-anatomy.html), and the Hero frosted-glass band.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const root = path.join(__dirname, "..");
const ratchet = JSON.parse(fs.readFileSync(path.join(root, "browser", "ratchet.json"), "utf8"));
const totals = ratchet.totals;

test("hero places 3 interactive V8 isometric figures on a central frosted-glass band framed by text", async ({
  page,
}) => {
  await page.goto("/");

  const topBox = await page.locator(".ch-hero-band-top").boundingBox();
  const bandBox = await page.getByTestId("hero-v8-band").boundingBox();
  const bottomBox = await page.locator(".ch-hero-band-bottom").boundingBox();

  expect(topBox && bandBox && bottomBox).toBeTruthy();
  expect(bandBox.y).toBeGreaterThan(topBox.y + topBox.height - 4);
  expect(bottomBox.y).toBeGreaterThan(bandBox.y + bandBox.height - 4);

  const backdropFilter = await page
    .getByTestId("hero-v8-band")
    .evaluate((el) => getComputedStyle(el).backdropFilter || getComputedStyle(el).webkitBackdropFilter);
  expect(backdropFilter).toContain("blur");

  const frames = page.getByTestId("hero-v8-trio").locator("iframe");
  await expect(frames).toHaveCount(3);
  await expect(frames.nth(0)).toHaveAttribute("src", /anatomy-03-turbofan/);
  await expect(frames.nth(1)).toHaveAttribute("src", /anatomy-02-ignition/);
  await expect(frames.nth(2)).toHaveAttribute("src", /anatomy-04-orinoco/);

  // Switch hero band to ai-iso-skill pressable consoles and interact inside the TurboFan console
  await page.getByTestId("hero-iso-mode-iso").click();
  await expect(frames.nth(0)).toHaveAttribute("src", /iso-03-turbofan/);

  const tfFrame = page.frameLocator('[data-testid="hero-v8-trio"] iframe').first();
  await expect(tfFrame.locator("#readout")).toContainText("turbofan");
  await tfFrame.locator('[data-k="flt"]').dispatchEvent("pointerdown");
  await expect(tfFrame.locator("#readout")).toContainText("ignition");

  // Theme switch propagates to embedded hero iframes
  await page.getByTestId("theme-switch").click();
  await expect(tfFrame.locator("html")).toHaveAttribute("data-theme", "light");

  // Switch back to Anatomy benchtop rigs
  await page.getByTestId("hero-iso-mode-anatomy").click();
  await expect(frames.nth(0)).toHaveAttribute("src", /anatomy-03-turbofan/);
});

test("v8-anatomy.html loads live ratchet telemetry, filters both styles, and handles missing data", async ({
  page,
}) => {
  const rawGallery = fs.readFileSync(path.join(root, "v8-anatomy.html"), "utf8");
  expect(rawGallery).not.toContain(String(totals.verified));
  expect(rawGallery).not.toContain(totals.verified.toLocaleString("en-US"));

  await page.goto("/v8-anatomy.html");
  await expect(page.getByTestId("gallery-ratchet-summary")).toContainText(
    totals.verified.toLocaleString("en-US")
  );
  await expect(page.getByTestId("counterpart-parser")).toContainText("proved");
  await expect(page.getByTestId("counterpart-liftoff")).toContainText("vwasm");

  // Filter controls toggle visibility between Anatomy rigs and ai-iso-skill consoles
  await page.getByTestId("filter-anatomy").click();
  await expect(page.locator('.fig-col[data-kind="anatomy"]').first()).toBeVisible();
  await expect(page.locator('.fig-col[data-kind="iso"]').first()).toBeHidden();

  await page.getByTestId("filter-iso").click();
  await expect(page.locator('.fig-col[data-kind="iso"]').first()).toBeVisible();
  await expect(page.locator('.fig-col[data-kind="anatomy"]').first()).toBeHidden();

  await page.getByTestId("filter-both").click();
  await expect(page.locator('.fig-col[data-kind="anatomy"]').first()).toBeVisible();
  await expect(page.locator('.fig-col[data-kind="iso"]').first()).toBeVisible();

  // Theme toggle propagates to embedded frames
  await page.getByTestId("gallery-theme-toggle").click();
  await expect(page.locator("html")).toHaveAttribute("data-theme", "light");

  // Missing ratchet.json surfaces explicit error and not recorded
  await page.route("**/browser/ratchet.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.reload();
  await expect(page.getByTestId("gallery-load-error")).toBeVisible();
  await expect(page.getByTestId("gallery-ratchet-summary")).toContainText("not recorded");
});

test("all 10 standalone V8 isometric pages render cleanly and update state on interaction", async ({
  page,
}) => {
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));

  const anatomySlugs = [
    "anatomy-01-parser",
    "anatomy-02-ignition",
    "anatomy-03-turbofan",
    "anatomy-04-orinoco",
    "anatomy-05-liftoff",
  ];
  for (const slug of anatomySlugs) {
    await page.goto(`/v8-iso/pages/${slug}.html`);
    const stage = page.locator(".iso-stage");
    const readout = page.locator("[data-readout]");
    await expect(stage).toBeVisible();
    const before = await readout.textContent();
    await stage.focus();
    await page.keyboard.press("Space");
    await expect
      .poll(async () => await readout.textContent(), { timeout: 3000 })
      .not.toBe(before);
  }

  const isoChecks = [
    { slug: "iso-01-parser", key: "mode", expectText: "lazy" },
    { slug: "iso-02-ignition", key: "M2", expectText: "poly-2" },
    { slug: "iso-03-turbofan", key: "flt", expectText: "ignition" },
    { slug: "iso-04-orinoco", key: "sweep", expectText: "0 dead" },
    { slug: "iso-05-liftoff", key: "oob", expectText: "trap: oob contained" },
  ];
  for (const item of isoChecks) {
    await page.goto(`/v8-iso/pages/${item.slug}.html`);
    await expect(page.locator("#stage")).toBeVisible();
    await page.locator(`[data-k="${item.key}"]`).dispatchEvent("pointerdown");
    await expect(page.locator("#readout")).toContainText(item.expectText);
  }

  expect(errors).toEqual([]);
});
