// End-to-end tests for the irrigation console against a REAL local bridge (port 8797),
// a real Verus build of the controller, and (when NANVIX_HOST is set) a real Nanvix host.
const { test, expect } = require("@playwright/test");

const BRIDGE = "http://127.0.0.1:8797";
const PAGE = `/irrigation.html?bridge=${encodeURIComponent(BRIDGE)}`;
const status = async (request) => (await request.get(`${BRIDGE}/api/status`)).json();
const post = (request, path, data = {}) => request.post(`${BRIDGE}${path}`, { data, headers: { "Content-Type": "application/json" } });

test.describe.configure({ mode: "serial" });

test("without a bridge: setup instructions shown and every control disabled", async ({ page }) => {
  await page.goto("/irrigation.html?bridge=http://127.0.0.1:1");
  await expect(page.getByTestId("setup")).toBeVisible();
  await expect(page.getByTestId("conn")).toHaveAttribute("data-state", "offline");
  const enabled = await page.locator("button:enabled, input:enabled, select:enabled").count();
  expect(enabled).toBe(0);
});

test("verify & build runs Verus on the controller and reports the real result", async ({ page, request }) => {
  await post(request, "/api/reset");
  await page.goto(PAGE);
  await expect(page.getByTestId("conn")).toHaveAttribute("data-state", "online");
  await expect(page.getByTestId("setup")).toBeHidden();
  await page.getByTestId("btn-verify").click();
  await expect(page.locator("#verify-result")).toContainText(/\d+ verified, 0 errors/, { timeout: 90000 });
  const v = (await status(request)).garden.verification;
  expect(v.errors).toBe(0);
  expect(v.verified).toBeGreaterThan(0);
  await expect(page.locator("#verify-result")).toContainText(`${v.verified} verified`);
  await expect(page.getByTestId("joblog")).toContainText("verification results::");
});

test("macOS runtime: start, valve open/close via table and diagram, stop", async ({ page, request }) => {
  await page.goto(PAGE);
  const card = page.getByTestId("rt-macos");
  await card.locator('[data-act="start"]').click();
  await expect(card).toHaveAttribute("data-running", "true");
  expect((await status(request)).runtimes.macos.running).toBe(true);

  const row0 = page.locator('#zone-rows tr[data-zone="0"]');
  await row0.locator(".open-b").click();
  await expect.poll(async () => (await status(request)).runtimes.macos.state.open[0]).toBe(true);
  await expect(page.locator('#zones g[data-zone="0"]')).toHaveClass(/open/);
  await row0.locator(".close-b").click();
  await expect.poll(async () => (await status(request)).runtimes.macos.state.open[0]).toBe(false);

  // the valve icon in the diagram toggles too
  await page.locator('#zones g[data-zone="1"] .valve-btn').click();
  await expect.poll(async () => (await status(request)).runtimes.macos.state.open[1]).toBe(true);
  await page.locator('#zones g[data-zone="1"] .valve-btn').click();
  await expect.poll(async () => (await status(request)).runtimes.macos.state.open[1]).toBe(false);
});

test("verified pump limit: a third valve is denied by the controller", async ({ page, request }) => {
  await page.goto(PAGE);
  for (const z of [0, 1]) {
    await page.locator(`#zone-rows tr[data-zone="${z}"] .open-b`).click();
    await expect.poll(async () => (await status(request)).runtimes.macos.state.open[z]).toBe(true);
  }
  await page.locator('#zone-rows tr[data-zone="2"] .open-b').click();
  await expect(page.getByTestId("events")).toContainText("manual open Greenhouse: denied");
  const st = (await status(request)).runtimes.macos.state;
  expect(st.open.filter(Boolean).length).toBe(st.limits.max_open);
  expect(st.open[2]).toBe(false);
  for (const z of [0, 1]) await page.locator(`#zone-rows tr[data-zone="${z}"] .close-b`).click();
  await expect.poll(async () => (await status(request)).runtimes.macos.state.open.filter(Boolean).length).toBe(0);
});

test("zone thresholds and auto toggle persist in the bridge", async ({ page, request }) => {
  await page.goto(PAGE);
  const row = page.locator('#zone-rows tr[data-zone="3"]');
  await row.locator(".low").fill("20");
  await row.locator(".low").press("Enter");
  await row.locator(".low").blur();
  await expect.poll(async () => (await status(request)).garden.zones[3].low).toBe(20);
  await row.locator(".high").fill("80");
  await row.locator(".high").blur();
  await expect.poll(async () => (await status(request)).garden.zones[3].high).toBe(80);
  const before = (await status(request)).garden.zones[3].auto;
  await row.locator(".auto").click();
  await expect.poll(async () => (await status(request)).garden.zones[3].auto).toBe(!before);
});

test("simulation: tick speed, refill, driver, start and pause", async ({ page, request }) => {
  await page.goto(PAGE);
  await page.locator("#tick").fill("200");
  await page.locator("#tick").dispatchEvent("change");
  await expect.poll(async () => (await status(request)).garden.sim.tick_ms).toBe(200);
  await page.locator("#refill").fill("12");
  await page.locator("#refill").dispatchEvent("change");
  await expect.poll(async () => (await status(request)).garden.sim.refill_per_tick).toBe(12);
  await page.locator("#primary").selectOption("macos");
  await expect.poll(async () => (await status(request)).garden.sim.primary).toBe("macos");

  const t0 = (await status(request)).runtimes.macos.state.ticks;
  await page.getByTestId("btn-run").click();
  await expect.poll(async () => (await status(request)).runtimes.macos.state.ticks, { timeout: 15000 }).toBeGreaterThan(t0 + 3);
  await expect(page.getByTestId("btn-run")).toHaveText("Pause");
  await page.getByTestId("btn-run").click();
  await expect.poll(async () => (await status(request)).garden.sim.running).toBe(false);
  const t1 = (await status(request)).runtimes.macos.state.ticks;
  await page.waitForTimeout(1200);
  expect((await status(request)).runtimes.macos.state.ticks).toBeLessThanOrEqual(t1 + 1);
});

test("nanvix: check host reports the real Windows/WHP state", async ({ page, request }) => {
  const s = await status(request);
  test.skip(!s.runtimes.nanvix.host, "NANVIX_HOST not set for this run");
  await page.goto(PAGE);
  const before = s.runtimes.nanvix.probe.checked || 0;
  await page.getByTestId("rt-nanvix").locator('[data-act="probe"]').click();
  await expect.poll(async () => (await status(request)).runtimes.nanvix.probe.checked || 0, { timeout: 40000 }).toBeGreaterThan(before);
  const p = (await status(request)).runtimes.nanvix.probe;
  expect(p.reachable).toBe(true);
  await expect(page.getByTestId("rt-nanvix").locator(".probe")).toContainText("WHP");
});

test("nanvix: guest runs in the micro-VM and agrees with macOS", async ({ page, request }) => {
  const p = (await status(request)).runtimes.nanvix.probe;
  test.skip(!(p && p.reachable && p.guest_built), "Nanvix guest not built on the host yet");
  await page.goto(PAGE);
  const card = page.getByTestId("rt-nanvix");
  await card.locator('[data-act="start"]').click();
  await expect(card).toHaveAttribute("data-running", "true", { timeout: 90000 });
  // both runtimes restart from the same state only if macOS is restarted too
  await page.getByTestId("rt-macos").locator('[data-act="stop"]').click();
  await page.getByTestId("rt-macos").locator('[data-act="start"]').click();
  await page.locator('#zone-rows tr[data-zone="2"] .open-b').click();
  await expect.poll(async () => (await status(request)).runtimes.nanvix.state.open[2], { timeout: 30000 }).toBe(true);
  await expect(page.getByTestId("agree")).toContainText("in agreement");
  expect((await status(request)).runtimes.nanvix.state.runtime).toBe("nanvix");
  await card.locator('[data-act="stop"]').click();
  await expect(card).toHaveAttribute("data-running", "false");
});

test("reset clears the garden and stops controllers", async ({ page, request }) => {
  await page.goto(PAGE);
  page.once("dialog", (d) => d.accept());
  await page.locator("#btn-reset").click();
  await expect.poll(async () => (await status(request)).runtimes.macos.running).toBe(false);
  const s = await status(request);
  expect(s.garden.zones[3].low).toBe(35);
  await page.getByTestId("rt-macos").locator('[data-act="stop"]').isDisabled();
});
