// Stage runtime telemetry and Inkwork mechanical plates (turboprop + maglev) into dist/.
// The site fetches ratchet.json and stats.json at runtime; nothing is hard-coded in JS.
import { cpSync, existsSync, mkdirSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const dist = resolve(root, 'dist');
if (!existsSync(dist)) {
  console.error('dist/ not found — run vite build first');
  process.exit(1);
}

const entries = [
  { src: 'data', dest: 'data' },
  { src: 'browser/ratchet.json', dest: 'browser/ratchet.json' },
  { src: 'inkwork/dist', dest: 'inkwork' },
  { src: 'irrigation.html', dest: 'irrigation.html' },
  { src: 'irrigation.css', dest: 'irrigation.css' },
  { src: 'irrigation.js', dest: 'irrigation.js' },
  { src: 'styles.css', dest: 'styles.css' },
  { src: 'v8-anatomy.html', dest: 'v8-anatomy.html' },
  { src: 'v8-iso/pages', dest: 'v8-iso/pages' },
  { src: 'assets', dest: 'assets' },
];

for (const { src, dest } of entries) {
  const from = resolve(root, src);
  if (!existsSync(from)) {
    console.error(`missing ${src} — cannot stage a complete site`);
    process.exit(1);
  }
  const to = resolve(dist, dest);
  mkdirSync(dirname(to), { recursive: true });
  cpSync(from, to, { recursive: true });
  console.log(`staged ${src} -> ${dest}`);
}
