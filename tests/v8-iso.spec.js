// End-to-end Playwright verification for the upgraded iso-cad v2 3D Surface/Lathe/Loft/Tube
// kernel: 3 Aerospace/Automotive/Marine showcases (Jet Engine, Sports Car, Cruise Ship),
// all 8 unique V8 Tier-1 Mandatory Core 3D sculptures, v8-anatomy.html, and the Hero band.
const { test, expect } = require("@playwright/test");
const fs = require("fs");
const path = require("path");

const root = path.join(__dirname, "..");
const ratchet = JSON.parse(fs.readFileSync(path.join(root, "browser", "ratchet.json"), "utf8"));
const totals = ratchet.totals;

test("hero places 3 interactive Tier-1 V8 3D sculptures on a central frosted-glass band framed by text", async ({
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

  const mapFrame = page.frameLocator('[data-testid="hero-v8-trio"] iframe').first();
  await expect(mapFrame.locator("#readout")).toContainText("map#2");
  await mapFrame.locator('.cad-tag[data-k="del"]').dispatchEvent("pointerdown");
  await expect(mapFrame.locator("#readout")).toContainText("dictionary map");

  await page.getByTestId("theme-switch").click();
  await expect(mapFrame.locator("html")).toHaveAttribute("data-theme", "light");
});

test("v8-anatomy.html renders 3 vehicle CAD showcases + 8 unique V8 core sculptures, loads live ratchet data, and handles missing telemetry", async ({
  page,
}) => {
  const rawGallery = fs.readFileSync(path.join(root, "v8-anatomy.html"), "utf8");
  expect(rawGallery).not.toContain(String(totals.verified));
  expect(rawGallery).not.toContain(totals.verified.toLocaleString("en-US"));

  await page.goto("/v8-anatomy.html");
  await expect(page.getByTestId("gallery-ratchet-summary")).toContainText(
    totals.verified.toLocaleString("en-US")
  );

  // 3 vehicle CAD showcases + 8 V8 Mandatory Core cards = 11 unique embedded 3D iframes
  await expect(page.locator(".showcase-grid .machine-card")).toHaveCount(3);
  await expect(page.locator(".machines-grid .machine-card")).toHaveCount(8);
  const frameSrcs = await page
    .locator("iframe.fig-frame")
    .evaluateAll((els) => els.map((el) => el.getAttribute("src")));
  expect(new Set(frameSrcs).size).toBe(11);

  await expect(page.getByTestId("counterpart-isolate")).toContainText("proved");
  await expect(page.getByTestId("counterpart-pointer-tagging")).toContainText("vjs_types");
  await expect(page.getByTestId("counterpart-hidden-classes")).toContainText("vjs_object");
  await expect(page.getByTestId("counterpart-parser")).toContainText("vjs_syntax");
  await expect(page.getByTestId("counterpart-ignition")).toContainText("vjs_vm");
  await expect(page.getByTestId("counterpart-torque-csa")).toContainText("vjs_builtins");
  await expect(page.getByTestId("counterpart-old-space")).toContainText("vjs_gc");
  await expect(page.getByTestId("counterpart-new-space")).toContainText("vjs_gc");

  await expect(page.locator("body")).toHaveAttribute("data-cols", "2");
  await page.getByTestId("layout-1col").click();
  await expect(page.locator("body")).toHaveAttribute("data-cols", "1");
  await page.reload();
  await expect(page.locator("body")).toHaveAttribute("data-cols", "1");
  await page.getByTestId("layout-2col").click();
  await expect(page.locator("body")).toHaveAttribute("data-cols", "2");

  await page.getByTestId("gallery-theme-toggle").click();
  await expect(page.locator("html")).toHaveAttribute("data-theme", "light");
  const firstFrame = page.frameLocator("iframe.fig-frame").first();
  await expect(firstFrame.locator("html")).toHaveAttribute("data-theme", "light");

  await page.route("**/browser/ratchet.json", (r) => r.fulfill({ status: 404, body: "" }));
  await page.reload();
  await expect(page.getByTestId("gallery-load-error")).toBeVisible();
  await expect(page.getByTestId("gallery-ratchet-summary")).toContainText("not recorded");
});

test("all 3 aerospace/automotive/marine showcases and all 8 V8 3D CAD pages actuate and orbit cleanly", async ({
  page,
}) => {
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));

  const checks = [
    // Aerospace, Automotive & Marine CAD Showcases
    {
      slug: "showcase-01-jet-engine",
      btn: "rev",
      afterBtn: "reverse -",
      key: "c",
      afterKey: "cowled ·",
    },
    {
      slug: "showcase-02-sports-car",
      btn: "wing",
      afterBtn: "active aero",
      key: "s",
      afterKey: "steer -18°",
    },
    {
      slug: "showcase-03-cruise-ship",
      btn: "davit",
      afterBtn: "davit outboard",
      key: "p",
      afterKey: "pods -20°",
    },
    // 8 V8 Tier-1 Mandatory Core 3D Sculptures
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

    const beforeSvg = await stage.innerHTML();
    svgSignatures.add(beforeSvg);

    await page.locator(`.cad-tag[data-k="${item.btn}"]`).dispatchEvent("pointerdown");
    await expect(readout).toContainText(item.afterBtn);

    await stage.focus();
    await page.keyboard.press(item.key);
    await expect(readout).toContainText(item.afterKey);

    // Verify 3D orbit key "]" re-projects the 3D mesh from a new camera azimuth!
    const preOrbitSvg = await stage.innerHTML();
    await page.keyboard.press("]");
    const postOrbitSvg = await stage.innerHTML();
    expect(postOrbitSvg).not.toBe(preOrbitSvg);
  }

  expect(svgSignatures.size).toBe(11);
  expect(errors).toEqual([]);
});
