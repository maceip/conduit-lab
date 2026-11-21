import { execFileSync } from "node:child_process";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const auditFlag = process.argv.includes("--audit") ? ["--audit"] : [];

const ANATOMY_SCRIPTS = [
  "anatomy/01-parser.mjs",
  "anatomy/02-ignition.mjs",
  "anatomy/03-turbofan.mjs",
  "anatomy/04-orinoco.mjs",
  "anatomy/05-liftoff.mjs",
];

for (const rel of ANATOMY_SCRIPTS) {
  execFileSync(process.execPath, [join(HERE, rel), ...auditFlag], { stdio: "inherit" });
}
execFileSync(process.execPath, [join(HERE, "iso-figure/build-iso-figures.mjs")], { stdio: "inherit" });
