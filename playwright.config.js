// @ts-check
const { defineConfig } = require("@playwright/test");
const nanvixHost = process.env.NANVIX_HOST; // e.g. user@10.0.0.5; Nanvix tests skip without it
module.exports = defineConfig({
  testDir: "tests",
  timeout: 120000,
  workers: 1,
  use: { baseURL: "http://localhost:8766", channel: "chrome" },
  webServer: [
    // The showcase is a built React app (site/ -> dist/); data + irrigation are staged into dist.
    { command: "python3 -m http.server 8766 --directory dist", port: 8766, reuseExistingServer: true },
    {
      // A real bridge with its own state dir, so tests never touch ~/.conduit-lab.
      command: `python3 bridge/conduit_bridge.py --port 8797 --state-dir .playwright-bridge --no-save-config${nanvixHost ? ` --nanvix-host ${nanvixHost}` : ""}`,
      url: "http://127.0.0.1:8797/api/status",
      reuseExistingServer: false,
      timeout: 60000,
    },
  ],
});
