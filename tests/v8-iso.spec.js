// End-to-end Playwright verification for the 8 unique V8 Tier-1 Mandatory Core
// isometric figures (built with MrBongoC/ai-iso-skill), the standalone 8-machine
// gallery (v8-anatomy.html), and the central Hero frosted-glass band.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const root = path.join(__dirname, "..");
const ratchet = JSON.parse(fs.readFileSync(path.join(root, "browser", "ratchet.json"), "utf8"));
const totals = ratchet.totals;

test("hero places 3 interactive Tier-1 V8 isometric machines on a central frosted-glass band framed by text", async ({
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
  await expect(frames.nth(0)).toHaveAttribute("src", /fig-03-hidden-classes/);
  await expect(frames.nth(1)).toHaveAttribute("src", /fig-05-ignition/);
  await expect(frames.nth(2)).toHaveAttribute("src", /fig-07-old-space/);

  // Interact directly inside the embedded Hidden Classes Turret Punch Press iframe
  const mapFrame = page.frameLocator('[data-testid="hero-v8-trio"] iframe').first();
  await expect(mapFrame.locator("#readout")).toContainText("map#2");
  await mapFrame.locator('[data-k="del"]').dispatchEvent("pointerdown");
  await expect(mapFrame.locator("#readout")).toContainText("dictionary map");

  // Theme switch propagates to all embedded hero iframes
  await page.getByTestId("theme-switch").click();
  await expect(mapFrame.locator("html")).toHaveAttribute("data-theme", "light");
});

test("v8-anatomy.html renders all 8 unique Tier-1 machines, loads live ratchet data, toggles layout/theme, and handles missing telemetry", async ({
  page,
}) => {
  const rawGallery = fs.readFileSync(path.join(root, "v8-anatomy.html"), "utf8");
  expect(rawGallery).not.toContain(String(totals.verified));
  expect(rawGallery).not.toContain(totals.verified.toLocaleString("en-US"));

  await page.goto("/v8-anatomy.html");
  await expect(page.getByTestId("gallery-ratchet-summary")).toContainText(
    totals.verified.toLocaleString("en-US")
  );

  // All 8 unique Tier-1 cards & distinct iframes exist and resolve live crate proof counts
  const cards = page.locator(".machine-card");
  await expect(cards).toHaveCount(8);
  const frameSrcs = await page
    .locator("iframe.fig-frame")
    .evaluateAll((els) => els.map((el) => el.getAttribute("src")));
  expect(new Set(frameSrcs).size).toBe(8);

  await expect(page.getByTestId("counterpart-isolate")).toContainText("proved");
  await expect(page.getByTestId("counterpart-pointer-tagging")).toContainText("vjs_types");
  await expect(page.getByTestId("counterpart-hidden-classes")).toContainText("vjs_object");
  await expect(page.getByTestId("counterpart-parser")).toContainText("vjs_syntax");
  await expect(page.getByTestId("counterpart-ignition")).toContainText("vjs_vm");
  await expect(page.getByTestId("counterpart-torque-csa")).toContainText("vjs_builtins");
  await expect(page.getByTestId("counterpart-old-space")).toContainText("vjs_gc");
  await expect(page.getByTestId("counterpart-new-space")).toContainText("vjs_gc");

  // Column density toggle (2-up grid vs 1-up focus) updates body attribute and persists
  await expect(page.locator("body")).toHaveAttribute("data-cols", "2");
  await page.getByTestId("layout-1col").click();
  await expect(page.locator("body")).toHaveAttribute("data-cols", "1");
  await page.reload();
  await expect(page.locator("body")).toHaveAttribute("data-cols", "1");
  await page.getByTestId("layout-2col").click();
  await expect(page.locator("body")).toHaveAttribute("data-cols", "2");

  // Theme toggle updates page and propagates to embedded frames
  await page.getByTestId("gallery-theme-toggle").click();
  await expect(page.locator("html")).toHaveAttribute("data-theme", "light");
  const firstFrame = page.frameLocator("iframe.fig-frame").first();
  await expect(firstFrame.locator("html")).toHaveAttribute("data-theme", "light");

  // Missing ratchet.json surfaces explicit error banner and "not recorded"
  await page.route("**/browser/ratchet.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.reload();
  await expect(page.getByTestId("gallery-load-error")).toBeVisible();
  await expect(page.getByTestId("gallery-ratchet-summary")).toContainText("not recorded");
  await expect(page.getByTestId("counterpart-ignition")).toContainText("not recorded");
});

test("all 8 standalone Tier-1 ai-iso-skill pages render unique geometry and transition state on click and keyboard", async ({
  page,
}) => {
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));

  const checks = [
    {
      slug: "fig-01-isolate",
      btn: "t2",
      afterBtn: "contended · thread #1 locked",
      key: "d",
      afterKey: "0 tasks",
    },
    {
      slug: "fig-02-pointer-tagging",
      btn: "heap",
      afterBtn: "heapobj",
      key: "s",
      afterKey: "smi ·",
    },
    {
      slug: "fig-03-hidden-classes",
      btn: "z",
      afterBtn: "map#3 {x@+4, y@+8, z@+12}",
      key: "d",
      afterKey: "dictionary map",
    },
    {
      slug: "fig-04-parser",
      btn: "hot",
      afterBtn: "eager sort · 3 scopeinfo / 3 ast",
      key: "e",
      afterKey: "early syntax error",
    },
    {
      slug: "fig-05-ignition",
      btn: "cut",
      afterBtn: "ignition off · 0 kPa",
      key: "c",
      afterKey: "24v on",
    },
    {
      slug: "fig-06-torque-csa",
      btn: "strike",
      afterBtn: "station 1/4 · LoadIC_BytecodeHandler · 4 built-ins",
      key: "r",
      afterKey: "station 0/4",
    },
    {
      slug: "fig-07-old-space",
      btn: "sweep",
      afterBtn: "6 live / 0 dead",
      key: "c",
      afterKey: "0% frag",
    },
    {
      slug: "fig-08-new-space",
      btn: "scav",
      afterBtn: "5 dropped",
      key: "Escape",
      afterKey: "0 to-space / 0 dropped · 0 promoted",
    },
  ];

  const svgSignatures = new Set();
  for (const item of checks) {
    await page.goto(`/v8-iso/pages/${item.slug}.html`);
    const stage = page.locator("#stage");
    const readout = page.locator("#readout");
    await expect(stage).toBeVisible();

    // Ensure every single machine has completely distinct SVG markup
    const svgHtml = await stage.innerHTML();
    svgSignatures.add(svgHtml);

    await page.locator(`[data-k="${item.btn}"]`).dispatchEvent("pointerdown");
    await expect(readout).toContainText(item.afterBtn);

    await stage.focus();
    await page.keyboard.press(item.key);
    await expect(readout).toContainText(item.afterKey);
  }

  expect(svgSignatures.size).toBe(8);
  expect(errors).toEqual([]);
});
