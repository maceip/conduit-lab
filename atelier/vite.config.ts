import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
  server: { port: 5180, strictPort: true },
  build: {
    outDir: 'dist',
    sourcemap: true,
    rollupOptions: {
      output: {
        // `three` is the only heavy dependency and only the tier-2 scene
        // needs it, so it gets its own chunk instead of inflating the main
        // bundle past the warning threshold.
        manualChunks: {
          three: ['three'],
        },
      },
    },
  },
});
