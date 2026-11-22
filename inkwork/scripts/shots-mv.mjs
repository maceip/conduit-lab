/** Capture maglev at t=0 (assembled), section, t=1 (exploded) and the three-view sheet. */
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { browser, sleep } from './edge.mjs';

const base = process.argv[2] ?? 'http://localhost:5199/';
const out = process.argv[3] ?? '/tmp/mv-shots';
mkdirSync(out, { recursive: true });
const b = await browser(base, { width: 1440, height: 900 });
const shot = async (name) => {
  await sleep(400);
  const s = await b.send('Page.captureScreenshot', { format: 'png' });
  writeFileSync(join(out, `${name}.png`), Buffer.from(s.result.data, 'base64'));
  console.log('shot', name);
};
const step = (i) => b.eval(`(()=>{const s=[...document.querySelectorAll('.step-num')];s[${i}]?.closest('button').click()})()`);
await b.open('maglev', 5000);
await step(0); await sleep(9000); await shot('1-assembled-t0');
await step(1); await sleep(6000); await shot('2-section-t0');
await step(2); await sleep(5000); await shot('3-train');
await step(3); await sleep(11000); await shot('4-exploded-t1');
await b.eval(`[...document.querySelectorAll('.views button')].find(b=>b.textContent.trim()==='Drawing')?.click()`);
await sleep(3500); await shot('5-sheet');
const uniq = [...new Set(b.errors)];
console.log(uniq.length ? 'ERRORS:\n' + uniq.join('\n') : 'ZERO console errors');
b.close();
process.exit(uniq.length ? 1 : 0);
