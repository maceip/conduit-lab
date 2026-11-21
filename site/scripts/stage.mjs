// Stage the runtime data and the standalone irrigation demo into dist/ after vite build.
// The site fetches these at runtime; nothing is bundled into the JS, so the
// "no hand-typed numbers" guarantee stays intact.
import { cpSync, existsSync, mkdirSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const dist = resolve(root, 'dist');
if (!existsSync(dist)) {
  console.error('dist/ not found — run vite build first');
  process.exit(1);
}

const files = [
  'data',
  'browser/ratchet.json',
  'irrigation.html',
  'irrigation.css',
  'irrigation.js',
  'styles.css', // irrigation.html still links the legacy stylesheet
  'assets',
];

for (const rel of files) {
  const src = resolve(root, rel);
  if (!existsSync(src)) {
    console.error(`missing ${rel} — cannot stage a complete site`);
    process.exit(1);
  }
  const dest = resolve(dist, rel);
  mkdirSync(dirname(dest), { recursive: true });
  cpSync(src, dest, { recursive: true });
  console.log(`staged ${rel}`);
}