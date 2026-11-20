// @ts-check
const { defineConfig } = require("@playwright/test");
module.exports = defineConfig({
  testDir: "tests",
  use: { baseURL: "http://localhost:8766", channel: "chrome" },
  webServer: { command: "python3 -m http.server 8766", port: 8766, reuseExistingServer: true },
});
