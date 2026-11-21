import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';

// The primitives are consumed from source, not npm (the package is unpublished).
// Local dev: ~/ix-workbench-primitives next to ~/conduit-lab.
// CI: actions/checkout places maceip/ix-workbench-primitives inside the repo.
const candidates = [
  resolve(__dirname, '../../ix-workbench-primitives'),
  resolve(__dirname, '../ix-workbench-primitives'),
];
const primitives = candidates.find((p) => existsSync(resolve(p, 'src/index.ts')));
if (!primitives) {
  throw new Error(
    `ix-workbench-primitives source not found. Looked in:\n  ${candidates.join('\n  ')}\n` +
      'Clone https://github.com/maceip/ix-workbench-primitives next to conduit-lab (or into conduit-lab/ in CI).',
  );
}

export default defineConfig({
  plugins: [react()],
  base: './',
  publicDir: false,
  resolve: {
    alias: {
      '@maceip/ix-workbench-primitives/styles.css': resolve(primitives, 'src/ix-workbench.css'),
      '@maceip/ix-workbench-primitives': resolve(primitives, 'src/index.ts'),
    },
    dedupe: ['react', 'react-dom'],
  },
  build: {
    outDir: '../dist',
    emptyOutDir: true,
  },
});